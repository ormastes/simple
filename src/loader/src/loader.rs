use std::fs::File;
use std::io::{Read, Seek, SeekFrom};
use std::path::Path;

use thiserror::Error;

use simple_common::DynLoader;

use crate::memory::*;
use crate::module::LoadedModule;
use crate::smf::*;

pub struct ModuleLoader {
    #[cfg(unix)]
    allocator: LinuxAllocator,
    #[cfg(windows)]
    allocator: WindowsAllocator,
}

impl ModuleLoader {
    pub fn new() -> Self {
        Self {
            #[cfg(unix)]
            allocator: LinuxAllocator::new(),
            #[cfg(windows)]
            allocator: WindowsAllocator::new(),
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

        // Read header
        let header = SmfHeader::read(&mut file)?;
        self.validate_header(&header)?;

        // Read sections
        file.seek(SeekFrom::Start(header.section_table_offset))?;
        let sections = self.read_sections(&mut file, header.section_count)?;

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
                    file.seek(SeekFrom::Start(section.offset))?;
                    let slice = unsafe {
                        std::slice::from_raw_parts_mut(
                            code_mem.as_mut_ptr().add(code_offset),
                            section.size as usize,
                        )
                    };
                    file.read_exact(slice)?;

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
                        file.seek(SeekFrom::Start(section.offset))?;
                        let slice = unsafe {
                            std::slice::from_raw_parts_mut(
                                data_mem.as_mut_ptr().add(data_offset),
                                section.size as usize,
                            )
                        };
                        file.read_exact(slice)?;

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
        let symbols = self.read_symbols(&mut file, &header)?;

        // Read relocations
        let relocs = self.read_relocations(&mut file, &sections)?;

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
            path: path.to_path_buf(),
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

    fn read_sections(&self, file: &mut File, count: u32) -> Result<Vec<SmfSection>, LoadError> {
        let mut sections = Vec::with_capacity(count as usize);

        for _ in 0..count {
            let mut buf = [0u8; std::mem::size_of::<SmfSection>()];
            file.read_exact(&mut buf)?;
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

    fn read_symbols(&self, file: &mut File, header: &SmfHeader) -> Result<SymbolTable, LoadError> {
        file.seek(SeekFrom::Start(header.symbol_table_offset))?;

        let mut symbols = Vec::with_capacity(header.symbol_count as usize);
        for _ in 0..header.symbol_count {
            let mut buf = [0u8; std::mem::size_of::<SmfSymbol>()];
            file.read_exact(&mut buf)?;
            let sym: SmfSymbol = unsafe { std::ptr::read(buf.as_ptr() as *const SmfSymbol) };
            symbols.push(sym);
        }

        // Read string table (follows symbols)
        let mut string_table = Vec::new();
        file.read_to_end(&mut string_table)?;

        Ok(SymbolTable::new(symbols, string_table))
    }

    fn read_relocations(
        &self,
        file: &mut File,
        sections: &[SmfSection],
    ) -> Result<Vec<SmfRelocation>, LoadError> {
        let mut relocs = Vec::new();

        for section in sections {
            if section.section_type == SectionType::Reloc {
                file.seek(SeekFrom::Start(section.offset))?;

                let count = section.size as usize / std::mem::size_of::<SmfRelocation>();
                for _ in 0..count {
                    let mut buf = [0u8; std::mem::size_of::<SmfRelocation>()];
                    file.read_exact(&mut buf)?;
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
