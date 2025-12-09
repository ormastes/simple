use std::fs::File;
use std::io::{Cursor, Read, Seek, SeekFrom};
use std::path::{Path, PathBuf};

use thiserror::Error;

use simple_common::DynLoader;

use crate::memory::*;
use crate::module::LoadedModule;
use crate::smf::*;

pub struct ModuleLoader {
    allocator: PlatformAllocator,
}

impl ModuleLoader {
    pub fn new() -> Self {
        Self {
            allocator: PlatformAllocator::new(),
        }
    }

    /// Load an SMF module from file
    pub fn load(&self, path: &Path) -> Result<LoadedModule, LoadError> {
        self.load_with_resolver(path, |_name| None)
    }

    /// Load an SMF module from file using a custom import resolver.
    /// The resolver is called for every non-local symbol reference during relocation.
    pub fn load_with_resolver<F>(
        &self,
        path: &Path,
        resolver: F,
    ) -> Result<LoadedModule, LoadError>
    where
        F: Fn(&str) -> Option<usize>,
    {
        let mut file = File::open(path)?;
        self.load_from_reader(&mut file, Some(path.to_path_buf()), resolver)
    }

    /// Load an SMF module from a memory buffer
    pub fn load_from_memory(&self, bytes: &[u8]) -> Result<LoadedModule, LoadError> {
        self.load_from_memory_with_resolver(bytes, |_name| None)
    }

    /// Load an SMF module from a memory buffer using a custom import resolver.
    pub fn load_from_memory_with_resolver<F>(
        &self,
        bytes: &[u8],
        resolver: F,
    ) -> Result<LoadedModule, LoadError>
    where
        F: Fn(&str) -> Option<usize>,
    {
        let mut cursor = Cursor::new(bytes);
        self.load_from_reader(&mut cursor, None, resolver)
    }

    /// Internal: Load from any Read+Seek source
    fn load_from_reader<R, F>(
        &self,
        reader: &mut R,
        path: Option<PathBuf>,
        resolver: F,
    ) -> Result<LoadedModule, LoadError>
    where
        R: Read + Seek,
        F: Fn(&str) -> Option<usize>,
    {
        // Read header
        let header = SmfHeader::read(reader)?;
        self.validate_header(&header)?;

        // Read sections
        reader.seek(SeekFrom::Start(header.section_table_offset))?;
        let sections = self.read_sections(reader, header.section_count)?;

        // Calculate total memory needed
        let (code_size, data_size) = self.calculate_sizes(&sections);

        // Allocate memory
        let code_mem = self.allocator.allocate(code_size, 4096)?;
        let data_mem = if data_size > 0 {
            Some(self.allocator.allocate(data_size, 4096)?)
        } else {
            None
        };

        // Load sections
        let mut code_offset = 0usize;
        let mut data_offset = 0usize;

        for section in &sections {
            match section.section_type {
                SectionType::Code => {
                    reader.seek(SeekFrom::Start(section.offset))?;
                    let slice = unsafe {
                        std::slice::from_raw_parts_mut(
                            code_mem.as_mut_ptr().add(code_offset),
                            section.size as usize,
                        )
                    };
                    reader.read_exact(slice)?;

                    // Zero any padding up to virtual size
                    if section.virtual_size > section.size {
                        let extra = section.virtual_size as usize - section.size as usize;
                        let pad_slice = unsafe {
                            std::slice::from_raw_parts_mut(
                                code_mem.as_mut_ptr().add(code_offset + section.size as usize),
                                extra,
                            )
                        };
                        pad_slice.fill(0);
                    }

                    code_offset += section.virtual_size as usize;
                }

                SectionType::Data | SectionType::RoData => {
                    if let Some(ref data_mem) = data_mem {
                        reader.seek(SeekFrom::Start(section.offset))?;
                        let slice = unsafe {
                            std::slice::from_raw_parts_mut(
                                data_mem.as_mut_ptr().add(data_offset),
                                section.size as usize,
                            )
                        };
                        reader.read_exact(slice)?;

                        if section.virtual_size > section.size {
                            let extra = section.virtual_size as usize - section.size as usize;
                            let pad_slice = unsafe {
                                std::slice::from_raw_parts_mut(
                                    data_mem.as_mut_ptr().add(data_offset + section.size as usize),
                                    extra,
                                )
                            };
                            pad_slice.fill(0);
                        }

                        data_offset += section.virtual_size as usize;
                    }
                }

                SectionType::Bss => {
                    if data_mem.is_some() {
                        let extra = section.virtual_size as usize;
                        let slice = unsafe {
                            std::slice::from_raw_parts_mut(
                                data_mem.as_ref().unwrap().as_mut_ptr().add(data_offset),
                                extra,
                            )
                        };
                        slice.fill(0);
                        data_offset += section.virtual_size as usize;
                    }
                }

                _ => {}
            }
        }

        // Read symbol table
        let symbols = self.read_symbols(reader, &header)?;

        // Read relocations
        let relocs = self.read_relocations(reader, &sections)?;

        // Apply relocations
        let code_slice = unsafe { std::slice::from_raw_parts_mut(code_mem.as_mut_ptr(), code_size) };

        apply_relocations(
            code_slice,
            &relocs,
            &symbols,
            code_mem.as_ptr() as usize,
            &resolver,
        )?;

        // Set memory protection
        self.allocator
            .protect(&code_mem, Protection::READ_EXECUTE)?;
        if let Some(ref data_mem) = data_mem {
            self.allocator
                .protect(data_mem, Protection::READ_WRITE)?;
        }

        Ok(LoadedModule {
            path: path.unwrap_or_else(|| PathBuf::from("<memory>")),
            header,
            code_mem,
            data_mem,
            symbols,
            version: 1,
        })
    }

    fn validate_header(&self, header: &SmfHeader) -> Result<(), LoadError> {
        // Check platform compatibility
        #[cfg(target_os = "linux")]
        if header.platform != Platform::Any as u8 && header.platform != Platform::Linux as u8 {
            return Err(LoadError::IncompatiblePlatform);
        }

        #[cfg(target_os = "windows")]
        if header.platform != Platform::Any as u8 && header.platform != Platform::Windows as u8 {
            return Err(LoadError::IncompatiblePlatform);
        }

        // Check architecture
        #[cfg(target_arch = "x86_64")]
        if header.arch != Arch::X86_64 as u8 {
            return Err(LoadError::IncompatibleArch);
        }

        Ok(())
    }

    fn read_sections<R: Read>(&self, reader: &mut R, count: u32) -> Result<Vec<SmfSection>, LoadError> {
        let mut sections = Vec::with_capacity(count as usize);

        for _ in 0..count {
            let mut buf = [0u8; std::mem::size_of::<SmfSection>()];
            reader.read_exact(&mut buf)?;
            let section: SmfSection = unsafe { std::ptr::read(buf.as_ptr() as *const SmfSection) };
            sections.push(section);
        }

        Ok(sections)
    }

    fn calculate_sizes(&self, sections: &[SmfSection]) -> (usize, usize) {
        let mut code_size = 0usize;
        let mut data_size = 0usize;

        for section in sections {
            match section.section_type {
                SectionType::Code => {
                    code_size += section.virtual_size as usize;
                }
                SectionType::Data | SectionType::RoData | SectionType::Bss => {
                    data_size += section.virtual_size as usize;
                }
                _ => {}
            }
        }

        // Align to page size
        let page_size = 4096;
        code_size = (code_size + page_size - 1) & !(page_size - 1);
        data_size = (data_size + page_size - 1) & !(page_size - 1);

        (code_size, data_size)
    }

    fn read_symbols<R: Read + Seek>(&self, reader: &mut R, header: &SmfHeader) -> Result<SymbolTable, LoadError> {
        reader.seek(SeekFrom::Start(header.symbol_table_offset))?;

        let mut symbols = Vec::with_capacity(header.symbol_count as usize);
        for _ in 0..header.symbol_count {
            let mut buf = [0u8; std::mem::size_of::<SmfSymbol>()];
            reader.read_exact(&mut buf)?;
            let sym: SmfSymbol = unsafe { std::ptr::read(buf.as_ptr() as *const SmfSymbol) };
            symbols.push(sym);
        }

        // Read string table (follows symbols)
        let mut string_table = Vec::new();
        reader.read_to_end(&mut string_table)?;

        Ok(SymbolTable::new(symbols, string_table))
    }

    fn read_relocations<R: Read + Seek>(
        &self,
        reader: &mut R,
        sections: &[SmfSection],
    ) -> Result<Vec<SmfRelocation>, LoadError> {
        let mut relocs = Vec::new();

        for section in sections {
            if section.section_type == SectionType::Reloc {
                reader.seek(SeekFrom::Start(section.offset))?;

                let count = section.size as usize / std::mem::size_of::<SmfRelocation>();
                for _ in 0..count {
                    let mut buf = [0u8; std::mem::size_of::<SmfRelocation>()];
                    reader.read_exact(&mut buf)?;
                    let reloc: SmfRelocation =
                        unsafe { std::ptr::read(buf.as_ptr() as *const SmfRelocation) };
                    relocs.push(reloc);
                }
            }
        }

        Ok(relocs)
    }
}

impl DynLoader for ModuleLoader {
    type Module = LoadedModule;
    type Error = LoadError;

    fn load(&self, path: &Path) -> Result<Self::Module, Self::Error> {
        self.load_with_resolver(path, |_name| None)
    }

    fn load_with_resolver<F>(&self, path: &Path, resolver: F) -> Result<Self::Module, Self::Error>
    where
        F: Fn(&str) -> Option<usize>,
    {
        ModuleLoader::load_with_resolver(self, path, resolver)
    }
}

#[derive(Debug, Error)]
pub enum LoadError {
    #[error("io error: {0}")]
    Io(#[from] std::io::Error),
    #[error("invalid format: {0}")]
    InvalidFormat(String),
    #[error("incompatible platform")]
    IncompatiblePlatform,
    #[error("incompatible architecture")]
    IncompatibleArch,
    #[error("undefined symbol: {0}")]
    UndefinedSymbol(String),
    #[error("relocation failed: {0}")]
    RelocationFailed(String),
}

impl From<String> for LoadError {
    fn from(e: String) -> Self {
        LoadError::RelocationFailed(e)
    }
}
