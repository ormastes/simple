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
    pub fn load_with_resolver<F>(&self, path: &Path, resolver: F) -> Result<LoadedModule, LoadError>
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
                    let section_size = section.size as usize;
                    let virtual_size = section.virtual_size as usize;

                    // Bounds check: code_offset + section_size must fit in code_mem
                    if code_offset.checked_add(section_size).map_or(true, |end| end > code_size) {
                        return Err(LoadError::BufferOverflow {
                            offset: code_offset,
                            size: section_size,
                            buffer_len: code_size,
                        });
                    }

                    reader.seek(SeekFrom::Start(section.offset))?;
                    let slice = unsafe {
                        std::slice::from_raw_parts_mut(
                            code_mem.as_mut_ptr().add(code_offset),
                            section_size,
                        )
                    };
                    reader.read_exact(slice)?;

                    // Zero any padding up to virtual size
                    if section.virtual_size > section.size {
                        let extra = virtual_size - section_size;
                        let pad_start = code_offset + section_size;

                        // Bounds check: pad region must fit in code_mem
                        if pad_start.checked_add(extra).map_or(true, |end| end > code_size) {
                            return Err(LoadError::BufferOverflow {
                                offset: pad_start,
                                size: extra,
                                buffer_len: code_size,
                            });
                        }

                        let pad_slice = unsafe {
                            std::slice::from_raw_parts_mut(
                                code_mem
                                    .as_mut_ptr()
                                    .add(pad_start),
                                extra,
                            )
                        };
                        pad_slice.fill(0);
                    }

                    code_offset += virtual_size;
                }

                SectionType::Data | SectionType::RoData => {
                    if let Some(ref data_mem) = data_mem {
                        let section_size = section.size as usize;
                        let virtual_size = section.virtual_size as usize;

                        // Bounds check: data_offset + section_size must fit in data_mem
                        if data_offset.checked_add(section_size).map_or(true, |end| end > data_size) {
                            return Err(LoadError::BufferOverflow {
                                offset: data_offset,
                                size: section_size,
                                buffer_len: data_size,
                            });
                        }

                        reader.seek(SeekFrom::Start(section.offset))?;
                        let slice = unsafe {
                            std::slice::from_raw_parts_mut(
                                data_mem.as_mut_ptr().add(data_offset),
                                section_size,
                            )
                        };
                        reader.read_exact(slice)?;

                        if section.virtual_size > section.size {
                            let extra = virtual_size - section_size;
                            let pad_start = data_offset + section_size;

                            // Bounds check: pad region must fit in data_mem
                            if pad_start.checked_add(extra).map_or(true, |end| end > data_size) {
                                return Err(LoadError::BufferOverflow {
                                    offset: pad_start,
                                    size: extra,
                                    buffer_len: data_size,
                                });
                            }

                            let pad_slice = unsafe {
                                std::slice::from_raw_parts_mut(
                                    data_mem
                                        .as_mut_ptr()
                                        .add(pad_start),
                                    extra,
                                )
                            };
                            pad_slice.fill(0);
                        }

                        data_offset += virtual_size;
                    }
                }

                SectionType::Bss => {
                    if let Some(ref data_mem) = data_mem {
                        let extra = section.virtual_size as usize;

                        // Bounds check: data_offset + extra must fit in data_mem
                        if data_offset.checked_add(extra).map_or(true, |end| end > data_size) {
                            return Err(LoadError::BufferOverflow {
                                offset: data_offset,
                                size: extra,
                                buffer_len: data_size,
                            });
                        }

                        let slice = unsafe {
                            std::slice::from_raw_parts_mut(
                                data_mem.as_mut_ptr().add(data_offset),
                                extra,
                            )
                        };
                        slice.fill(0);
                        data_offset += extra;
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
        // Safety: code_size was used to allocate code_mem, so this is within bounds
        if code_size > code_mem.size() {
            return Err(LoadError::BufferOverflow {
                offset: 0,
                size: code_size,
                buffer_len: code_mem.size(),
            });
        }
        let code_slice =
            unsafe { std::slice::from_raw_parts_mut(code_mem.as_mut_ptr(), code_size) };

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
            self.allocator.protect(data_mem, Protection::READ_WRITE)?;
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

    fn read_sections<R: Read>(
        &self,
        reader: &mut R,
        count: u32,
    ) -> Result<Vec<SmfSection>, LoadError> {
        // Guard against excessive section counts that could cause OOM
        const MAX_SECTIONS: u32 = 65536;
        if count > MAX_SECTIONS {
            return Err(LoadError::InvalidFormat(format!(
                "section count {} exceeds maximum {}",
                count, MAX_SECTIONS
            )));
        }

        let mut sections = Vec::with_capacity(count as usize);

        for i in 0..count {
            let mut buf = [0u8; std::mem::size_of::<SmfSection>()];
            reader.read_exact(&mut buf)?;

            // Safety: buf is exactly size_of::<SmfSection>() bytes, read from reader.
            // The buffer size matches the struct size, so ptr::read is within bounds.
            debug_assert!(buf.len() == std::mem::size_of::<SmfSection>());
            let section: SmfSection = unsafe { std::ptr::read(buf.as_ptr() as *const SmfSection) };

            // Validate section fields to catch corrupted data early
            if section.size > section.virtual_size && section.virtual_size != 0 {
                return Err(LoadError::InvalidFormat(format!(
                    "section {} has size {} > virtual_size {}",
                    i, section.size, section.virtual_size
                )));
            }

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

    fn read_symbols<R: Read + Seek>(
        &self,
        reader: &mut R,
        header: &SmfHeader,
    ) -> Result<SymbolTable, LoadError> {
        // Guard against excessive symbol counts that could cause OOM
        const MAX_SYMBOLS: u32 = 1_000_000;
        if header.symbol_count > MAX_SYMBOLS {
            return Err(LoadError::InvalidFormat(format!(
                "symbol count {} exceeds maximum {}",
                header.symbol_count, MAX_SYMBOLS
            )));
        }

        reader.seek(SeekFrom::Start(header.symbol_table_offset))?;

        let mut symbols = Vec::with_capacity(header.symbol_count as usize);
        for _ in 0..header.symbol_count {
            let mut buf = [0u8; std::mem::size_of::<SmfSymbol>()];
            reader.read_exact(&mut buf)?;

            // Safety: buf is exactly size_of::<SmfSymbol>() bytes.
            // The buffer size matches the struct size, so ptr::read is within bounds.
            debug_assert!(buf.len() == std::mem::size_of::<SmfSymbol>());
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

                let reloc_size = std::mem::size_of::<SmfRelocation>();
                if reloc_size == 0 {
                    return Err(LoadError::InvalidFormat(
                        "SmfRelocation has zero size".to_string(),
                    ));
                }
                let section_size = section.size as usize;

                // Validate section size is a multiple of relocation entry size
                if section_size % reloc_size != 0 {
                    return Err(LoadError::InvalidFormat(format!(
                        "relocation section size {} is not a multiple of entry size {}",
                        section_size, reloc_size
                    )));
                }

                let count = section_size / reloc_size;

                // Guard against excessive relocation counts
                const MAX_RELOCATIONS: usize = 10_000_000;
                if count > MAX_RELOCATIONS {
                    return Err(LoadError::InvalidFormat(format!(
                        "relocation count {} exceeds maximum {}",
                        count, MAX_RELOCATIONS
                    )));
                }

                for _ in 0..count {
                    let mut buf = [0u8; std::mem::size_of::<SmfRelocation>()];
                    reader.read_exact(&mut buf)?;

                    // Safety: buf is exactly size_of::<SmfRelocation>() bytes.
                    // The buffer size matches the struct size, so ptr::read is within bounds.
                    debug_assert!(buf.len() == std::mem::size_of::<SmfRelocation>());
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
    #[error("buffer overflow: offset {offset} + size {size} exceeds buffer length {buffer_len}")]
    BufferOverflow {
        offset: usize,
        size: usize,
        buffer_len: usize,
    },
}

impl From<String> for LoadError {
    fn from(e: String) -> Self {
        LoadError::RelocationFailed(e)
    }
}
