use std::fs::File;
use std::io::{Cursor, Read, Seek, SeekFrom};
use std::path::{Path, PathBuf};

use thiserror::Error;
use tracing::{debug, error, instrument, trace, warn};

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
    #[instrument(skip(self), fields(path = %path.display()))]
    pub fn load(&self, path: &Path) -> Result<LoadedModule, LoadError> {
        debug!("Loading SMF module from file");
        self.load_with_resolver(path, |_name| None)
    }

    /// Load an SMF module from file using a custom import resolver.
    /// The resolver is called for every non-local symbol reference during relocation.
    #[instrument(skip(self, resolver), fields(path = %path.display()))]
    pub fn load_with_resolver<F>(&self, path: &Path, resolver: F) -> Result<LoadedModule, LoadError>
    where
        F: Fn(&str) -> Option<usize>,
    {
        debug!("Opening file for SMF loading");
        let mut file = File::open(path).map_err(|e| {
            error!(error = %e, "Failed to open SMF file");
            LoadError::Io(e)
        })?;
        trace!("File opened successfully, delegating to reader");
        self.load_from_reader(&mut file, Some(path.to_path_buf()), resolver)
    }

    /// Load an SMF module from a memory buffer
    #[instrument(skip(self, bytes), fields(size = bytes.len()))]
    pub fn load_from_memory(&self, bytes: &[u8]) -> Result<LoadedModule, LoadError> {
        debug!("Loading SMF module from memory buffer");
        self.load_from_memory_with_resolver(bytes, |_name| None)
    }

    /// Load an SMF module from a memory buffer using a custom import resolver.
    #[instrument(skip(self, bytes, resolver), fields(size = bytes.len()))]
    pub fn load_from_memory_with_resolver<F>(
        &self,
        bytes: &[u8],
        resolver: F,
    ) -> Result<LoadedModule, LoadError>
    where
        F: Fn(&str) -> Option<usize>,
    {
        debug!("Loading SMF from memory with custom resolver");
        let mut cursor = Cursor::new(bytes);
        self.load_from_reader(&mut cursor, None, resolver)
    }

    /// Internal: Load from any Read+Seek source
    #[instrument(skip(self, reader, resolver), fields(path = ?path))]
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
        debug!("Reading SMF header");
        let header = SmfHeader::read(reader).map_err(|e| {
            error!(error = %e, "Failed to read SMF header");
            e
        })?;
        trace!(
            section_count = header.section_count,
            symbol_count = header.symbol_count,
            "Header read successfully"
        );

        self.validate_header(&header).map_err(|e| {
            error!(error = %e, "Header validation failed");
            e
        })?;

        // Read sections
        debug!(
            offset = header.section_table_offset,
            count = header.section_count,
            "Reading section table"
        );
        reader.seek(SeekFrom::Start(header.section_table_offset)).map_err(|e| {
            error!(offset = header.section_table_offset, error = %e, "Failed to seek to section table");
            LoadError::Io(e)
        })?;
        let sections = self.read_sections(reader, header.section_count)?;
        trace!(sections = sections.len(), "Section table read successfully");

        // Calculate total memory needed
        let (code_size, data_size) = self.calculate_sizes(&sections);
        debug!(code_size, data_size, "Calculated memory sizes");

        if code_size == 0 {
            warn!("Module has no code section - this may be invalid");
        }

        // Allocate memory
        debug!(size = code_size, "Allocating code memory");
        let code_mem = self.allocator.allocate(code_size, 4096).map_err(|e| {
            error!(size = code_size, error = %e, "Failed to allocate code memory");
            e
        })?;

        let data_mem = if data_size > 0 {
            debug!(size = data_size, "Allocating data memory");
            Some(self.allocator.allocate(data_size, 4096).map_err(|e| {
                error!(size = data_size, error = %e, "Failed to allocate data memory");
                e
            })?)
        } else {
            trace!("No data section needed");
            None
        };

        // Load sections with bounds checking
        let mut code_offset = 0usize;
        let mut data_offset = 0usize;

        for (idx, section) in sections.iter().enumerate() {
            trace!(
                section_idx = idx,
                section_type = ?section.section_type,
                offset = section.offset,
                size = section.size,
                virtual_size = section.virtual_size,
                "Processing section"
            );

            match section.section_type {
                SectionType::Code => {
                    // Bounds check: ensure we won't overflow the code buffer
                    let section_size = section.size as usize;
                    let virtual_size = section.virtual_size as usize;
                    let end_offset = code_offset.checked_add(virtual_size).ok_or_else(|| {
                        error!(code_offset, virtual_size, "Code offset overflow");
                        LoadError::InvalidFormat("Code section offset overflow".to_string())
                    })?;

                    if end_offset > code_size {
                        error!(
                            end_offset,
                            code_size,
                            section_idx = idx,
                            "Code section exceeds allocated memory"
                        );
                        return Err(LoadError::InvalidFormat(format!(
                            "Code section {} at offset {} with size {} exceeds allocated code memory {}",
                            idx, code_offset, virtual_size, code_size
                        )));
                    }

                    reader.seek(SeekFrom::Start(section.offset)).map_err(|e| {
                        error!(offset = section.offset, error = %e, "Failed to seek to code section");
                        LoadError::Io(e)
                    })?;

                    let slice = unsafe {
                        std::slice::from_raw_parts_mut(
                            code_mem.as_mut_ptr().add(code_offset),
                            section_size,
                        )
                    };
                    reader.read_exact(slice).map_err(|e| {
                        error!(section_idx = idx, size = section_size, error = %e, "Failed to read code section");
                        LoadError::Io(e)
                    })?;

                    // Zero any padding up to virtual size
                    if virtual_size > section_size {
                        let extra = virtual_size - section_size;
                        trace!(extra, "Zeroing code section padding");
                        let pad_slice = unsafe {
                            std::slice::from_raw_parts_mut(
                                code_mem.as_mut_ptr().add(code_offset + section_size),
                                extra,
                            )
                        };
                        pad_slice.fill(0);
                    }

                    code_offset = end_offset;
                }

                SectionType::Data | SectionType::RoData => {
                    if let Some(ref data_mem) = data_mem {
                        let section_size = section.size as usize;
                        let virtual_size = section.virtual_size as usize;
                        let end_offset =
                            data_offset.checked_add(virtual_size).ok_or_else(|| {
                                error!(data_offset, virtual_size, "Data offset overflow");
                                LoadError::InvalidFormat("Data section offset overflow".to_string())
                            })?;

                        if end_offset > data_size {
                            error!(
                                end_offset,
                                data_size,
                                section_idx = idx,
                                "Data section exceeds allocated memory"
                            );
                            return Err(LoadError::InvalidFormat(format!(
                                "Data section {} at offset {} with size {} exceeds allocated data memory {}",
                                idx, data_offset, virtual_size, data_size
                            )));
                        }

                        reader.seek(SeekFrom::Start(section.offset)).map_err(|e| {
                            error!(offset = section.offset, error = %e, "Failed to seek to data section");
                            LoadError::Io(e)
                        })?;

                        let slice = unsafe {
                            std::slice::from_raw_parts_mut(
                                data_mem.as_mut_ptr().add(data_offset),
                                section_size,
                            )
                        };
                        reader.read_exact(slice).map_err(|e| {
                            error!(section_idx = idx, size = section_size, error = %e, "Failed to read data section");
                            LoadError::Io(e)
                        })?;

                        if virtual_size > section_size {
                            let extra = virtual_size - section_size;
                            trace!(extra, "Zeroing data section padding");
                            let pad_slice = unsafe {
                                std::slice::from_raw_parts_mut(
                                    data_mem.as_mut_ptr().add(data_offset + section_size),
                                    extra,
                                )
                            };
                            pad_slice.fill(0);
                        }

                        data_offset = end_offset;
                    }
                }

                SectionType::Bss => {
                    if let Some(ref data_mem) = data_mem {
                        let virtual_size = section.virtual_size as usize;
                        let end_offset =
                            data_offset.checked_add(virtual_size).ok_or_else(|| {
                                error!(data_offset, virtual_size, "BSS offset overflow");
                                LoadError::InvalidFormat("BSS section offset overflow".to_string())
                            })?;

                        if end_offset > data_size {
                            error!(
                                end_offset,
                                data_size,
                                section_idx = idx,
                                "BSS section exceeds allocated memory"
                            );
                            return Err(LoadError::InvalidFormat(format!(
                                "BSS section {} at offset {} with size {} exceeds allocated data memory {}",
                                idx, data_offset, virtual_size, data_size
                            )));
                        }

                        trace!(size = virtual_size, "Zeroing BSS section");
                        let slice = unsafe {
                            std::slice::from_raw_parts_mut(
                                data_mem.as_mut_ptr().add(data_offset),
                                virtual_size,
                            )
                        };
                        slice.fill(0);
                        data_offset = end_offset;
                    }
                }

                _ => {
                    trace!(section_type = ?section.section_type, "Skipping unknown section type");
                }
            }
        }

        // Read symbol table
        debug!(
            offset = header.symbol_table_offset,
            count = header.symbol_count,
            "Reading symbol table"
        );
        let symbols = self.read_symbols(reader, &header).map_err(|e| {
            error!(error = %e, "Failed to read symbol table");
            e
        })?;
        trace!(
            symbols = symbols.symbols.len(),
            "Symbol table read successfully"
        );

        // Read relocations
        debug!("Reading relocations");
        let relocs = self.read_relocations(reader, &sections).map_err(|e| {
            error!(error = %e, "Failed to read relocations");
            e
        })?;
        trace!(relocations = relocs.len(), "Relocations read successfully");

        // Apply relocations
        debug!(count = relocs.len(), "Applying relocations");
        let code_slice =
            unsafe { std::slice::from_raw_parts_mut(code_mem.as_mut_ptr(), code_size) };

        apply_relocations(
            code_slice,
            &relocs,
            &symbols,
            code_mem.as_ptr() as usize,
            &resolver,
        )
        .map_err(|e| {
            error!(error = %e, "Failed to apply relocations");
            LoadError::RelocationFailed(e)
        })?;
        trace!("Relocations applied successfully");

        // Set memory protection
        debug!("Setting memory protection for code section (READ_EXECUTE)");
        self.allocator
            .protect(&code_mem, Protection::READ_EXECUTE)
            .map_err(|e| {
                error!(error = %e, "Failed to set code memory protection");
                e
            })?;

        if let Some(ref data_mem) = data_mem {
            debug!("Setting memory protection for data section (READ_WRITE)");
            self.allocator
                .protect(data_mem, Protection::READ_WRITE)
                .map_err(|e| {
                    error!(error = %e, "Failed to set data memory protection");
                    e
                })?;
        }

        let module_path = path.unwrap_or_else(|| PathBuf::from("<memory>"));
        debug!(path = ?module_path, "Module loaded successfully");

        Ok(LoadedModule {
            path: module_path,
            header,
            code_mem,
            data_mem,
            symbols,
            version: 1,
        })
    }

    #[instrument(skip(self, header))]
    fn validate_header(&self, header: &SmfHeader) -> Result<(), LoadError> {
        trace!(
            platform = header.platform,
            arch = header.arch,
            "Validating header compatibility"
        );

        // Check platform compatibility
        #[cfg(target_os = "linux")]
        if header.platform != Platform::Any as u8 && header.platform != Platform::Linux as u8 {
            error!(
                expected = Platform::Linux as u8,
                got = header.platform,
                "Platform mismatch"
            );
            return Err(LoadError::IncompatiblePlatform);
        }

        #[cfg(target_os = "windows")]
        if header.platform != Platform::Any as u8 && header.platform != Platform::Windows as u8 {
            error!(
                expected = Platform::Windows as u8,
                got = header.platform,
                "Platform mismatch"
            );
            return Err(LoadError::IncompatiblePlatform);
        }

        // Check architecture
        #[cfg(target_arch = "x86_64")]
        if header.arch != Arch::X86_64 as u8 {
            error!(
                expected = Arch::X86_64 as u8,
                got = header.arch,
                "Architecture mismatch"
            );
            return Err(LoadError::IncompatibleArch);
        }

        trace!("Header validation passed");
        Ok(())
    }

    #[instrument(skip(self, reader))]
    fn read_sections<R: Read>(
        &self,
        reader: &mut R,
        count: u32,
    ) -> Result<Vec<SmfSection>, LoadError> {
        trace!(count, "Reading section table entries");
        let mut sections = Vec::with_capacity(count as usize);

        for i in 0..count {
            let mut buf = [0u8; std::mem::size_of::<SmfSection>()];
            reader.read_exact(&mut buf).map_err(|e| {
                error!(section_idx = i, error = %e, "Failed to read section entry");
                LoadError::Io(e)
            })?;
            let section: SmfSection = unsafe { std::ptr::read(buf.as_ptr() as *const SmfSection) };
            trace!(
                section_idx = i,
                section_type = ?section.section_type,
                offset = section.offset,
                size = section.size,
                "Read section entry"
            );
            sections.push(section);
        }

        trace!(count = sections.len(), "Section table read complete");
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
        let aligned_code_size = (code_size + page_size - 1) & !(page_size - 1);
        let aligned_data_size = (data_size + page_size - 1) & !(page_size - 1);

        trace!(
            raw_code = code_size,
            aligned_code = aligned_code_size,
            raw_data = data_size,
            aligned_data = aligned_data_size,
            "Calculated section sizes"
        );

        (aligned_code_size, aligned_data_size)
    }

    #[instrument(skip(self, reader, header))]
    fn read_symbols<R: Read + Seek>(
        &self,
        reader: &mut R,
        header: &SmfHeader,
    ) -> Result<SymbolTable, LoadError> {
        trace!(
            offset = header.symbol_table_offset,
            count = header.symbol_count,
            "Seeking to symbol table"
        );
        reader.seek(SeekFrom::Start(header.symbol_table_offset)).map_err(|e| {
            error!(offset = header.symbol_table_offset, error = %e, "Failed to seek to symbol table");
            LoadError::Io(e)
        })?;

        let mut symbols = Vec::with_capacity(header.symbol_count as usize);
        for i in 0..header.symbol_count {
            let mut buf = [0u8; std::mem::size_of::<SmfSymbol>()];
            reader.read_exact(&mut buf).map_err(|e| {
                error!(symbol_idx = i, error = %e, "Failed to read symbol entry");
                LoadError::Io(e)
            })?;
            let sym: SmfSymbol = unsafe { std::ptr::read(buf.as_ptr() as *const SmfSymbol) };
            trace!(
                symbol_idx = i,
                name_offset = sym.name_offset,
                sym_type = ?sym.sym_type,
                value = sym.value,
                "Read symbol entry"
            );
            symbols.push(sym);
        }

        // Read string table (follows symbols)
        trace!("Reading string table");
        let mut string_table = Vec::new();
        reader.read_to_end(&mut string_table).map_err(|e| {
            error!(error = %e, "Failed to read string table");
            LoadError::Io(e)
        })?;
        trace!(
            string_table_size = string_table.len(),
            "String table read complete"
        );

        Ok(SymbolTable::new(symbols, string_table))
    }

    #[instrument(skip(self, reader, sections))]
    fn read_relocations<R: Read + Seek>(
        &self,
        reader: &mut R,
        sections: &[SmfSection],
    ) -> Result<Vec<SmfRelocation>, LoadError> {
        let mut relocs = Vec::new();

        for (section_idx, section) in sections.iter().enumerate() {
            if section.section_type == SectionType::Reloc {
                trace!(
                    section_idx,
                    offset = section.offset,
                    size = section.size,
                    "Found relocation section"
                );
                reader.seek(SeekFrom::Start(section.offset)).map_err(|e| {
                    error!(
                        section_idx,
                        offset = section.offset,
                        error = %e,
                        "Failed to seek to relocation section"
                    );
                    LoadError::Io(e)
                })?;

                let count = section.size as usize / std::mem::size_of::<SmfRelocation>();
                trace!(count, "Reading relocation entries");

                for i in 0..count {
                    let mut buf = [0u8; std::mem::size_of::<SmfRelocation>()];
                    reader.read_exact(&mut buf).map_err(|e| {
                        error!(reloc_idx = i, error = %e, "Failed to read relocation entry");
                        LoadError::Io(e)
                    })?;
                    let reloc: SmfRelocation =
                        unsafe { std::ptr::read(buf.as_ptr() as *const SmfRelocation) };
                    trace!(
                        reloc_idx = i,
                        offset = reloc.offset,
                        symbol_index = reloc.symbol_index,
                        reloc_type = ?reloc.reloc_type,
                        "Read relocation entry"
                    );
                    relocs.push(reloc);
                }
            }
        }

        trace!(
            total_relocations = relocs.len(),
            "Finished reading relocations"
        );
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
