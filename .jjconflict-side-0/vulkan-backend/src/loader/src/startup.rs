//! Startup-only loader for settlement executables.
//!
//! This module provides a minimal loader that can execute settlement files
//! directly as executables. It's designed to be embedded in the executable stub.

use std::fs::File;
use std::io::{Read, Seek, SeekFrom};
use std::path::Path;
use std::sync::Arc;

use crate::memory::{ExecutableMemory, MemoryAllocator, PlatformAllocator, Protection};
use crate::settlement::{FunctionTable, GlobalTable, NativeLibManager, TableIndex};
use crate::smf::settlement::{
    NativeLibEntry, SettlementHeader, NATIVE_LIB_SHARED, NATIVE_LIB_SYSTEM, SSMF_FLAG_EXECUTABLE,
    SSMF_MAGIC,
};

/// Errors that can occur during startup loading.
#[derive(Debug)]
pub enum StartupError {
    IoError(std::io::Error),
    InvalidMagic,
    NotExecutable,
    InvalidHeader,
    MemoryAllocationFailed,
    NoEntryPoint,
    NativeLibLoadFailed(String),
}

impl std::fmt::Display for StartupError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StartupError::IoError(e) => write!(f, "I/O error: {}", e),
            StartupError::InvalidMagic => write!(f, "Invalid SSMF magic"),
            StartupError::NotExecutable => write!(f, "Settlement is not marked as executable"),
            StartupError::InvalidHeader => write!(f, "Invalid settlement header"),
            StartupError::MemoryAllocationFailed => write!(f, "Memory allocation failed"),
            StartupError::NoEntryPoint => write!(f, "No entry point defined"),
            StartupError::NativeLibLoadFailed(name) => {
                write!(f, "Failed to load native lib: {}", name)
            }
        }
    }
}

impl std::error::Error for StartupError {}

impl From<std::io::Error> for StartupError {
    fn from(e: std::io::Error) -> Self {
        StartupError::IoError(e)
    }
}

/// A loaded settlement ready for execution.
pub struct LoadedSettlement {
    /// Executable memory for code
    #[allow(dead_code)]
    code_mem: ExecutableMemory,
    /// Executable memory for data (read-write)
    #[allow(dead_code)]
    data_mem: ExecutableMemory,
    /// Function table
    func_table: FunctionTable,
    /// Global table
    global_table: GlobalTable,
    /// Native library manager
    #[allow(dead_code)]
    native_libs: NativeLibManager,
    /// Entry point function pointer
    entry_fn: Option<*const u8>,
    /// Memory allocator reference
    _allocator: Arc<dyn MemoryAllocator>,
}

// Safety: The pointers are valid for the lifetime of the settlement
unsafe impl Send for LoadedSettlement {}
unsafe impl Sync for LoadedSettlement {}

impl LoadedSettlement {
    /// Get the entry point function pointer.
    pub fn entry_point(&self) -> Option<*const u8> {
        self.entry_fn
    }

    /// Execute the entry point.
    ///
    /// # Safety
    /// The entry point must be a valid function pointer with the signature `fn() -> i32`.
    pub unsafe fn execute(&self) -> Result<i32, StartupError> {
        let entry = self.entry_fn.ok_or(StartupError::NoEntryPoint)?;
        let func: extern "C" fn() -> i32 = std::mem::transmute(entry);
        Ok(func())
    }

    /// Get a function pointer by table index.
    pub fn get_function(&self, idx: TableIndex) -> Option<*const u8> {
        self.func_table.get_code_ptr(idx).map(|p| p as *const u8)
    }

    /// Get a global data pointer by table index.
    pub fn get_global(&self, idx: TableIndex) -> Option<*mut u8> {
        self.global_table.get_data_ptr(idx).map(|p| p as *mut u8)
    }
}

/// Startup loader for settlement executables.
///
/// This is a minimal loader designed for fast startup. It reads a settlement
/// file (or the settlement data appended to an executable) and prepares it
/// for execution.
pub struct StartupLoader {
    allocator: Arc<dyn MemoryAllocator>,
}

impl StartupLoader {
    /// Create a new startup loader with the platform allocator.
    pub fn new() -> Self {
        Self {
            allocator: Arc::new(PlatformAllocator::new()),
        }
    }

    /// Create with a custom allocator.
    pub fn with_allocator(allocator: Arc<dyn MemoryAllocator>) -> Self {
        Self { allocator }
    }

    /// Load a settlement from a file path.
    pub fn load<P: AsRef<Path>>(&self, path: P) -> Result<LoadedSettlement, StartupError> {
        let mut file = File::open(path)?;
        self.load_from_file(&mut file, 0)
    }

    /// Load a settlement from the current executable.
    ///
    /// This finds the settlement data appended after the PE/ELF executable.
    pub fn load_from_self() -> Result<LoadedSettlement, StartupError> {
        let exe_path = std::env::current_exe()?;
        let loader = Self::new();

        let mut file = File::open(&exe_path)?;
        let offset = Self::find_settlement_offset(&mut file)?;

        loader.load_from_file(&mut file, offset)
    }

    /// Find the offset where settlement data begins in an executable.
    fn find_settlement_offset(file: &mut File) -> Result<u64, StartupError> {
        // Read file size
        let file_size = file.seek(SeekFrom::End(0))?;

        // For settlement executables, we store the offset at the end of the file
        // Format: [executable stub][settlement data][8-byte offset to settlement][8-byte magic "SSMFOFFS"]
        const TRAILER_SIZE: u64 = 16;

        if file_size < TRAILER_SIZE {
            return Err(StartupError::InvalidHeader);
        }

        // Read the trailer
        file.seek(SeekFrom::End(-(TRAILER_SIZE as i64)))?;
        let mut trailer = [0u8; 16];
        file.read_exact(&mut trailer)?;

        // Check magic
        if &trailer[8..16] != b"SSMFOFFS" {
            // No appended settlement - assume the file IS the settlement
            return Ok(0);
        }

        // Read offset
        let offset = u64::from_le_bytes(trailer[0..8].try_into().unwrap());

        Ok(offset)
    }

    /// Load a settlement from an open file at the given offset.
    fn load_from_file(
        &self,
        file: &mut File,
        offset: u64,
    ) -> Result<LoadedSettlement, StartupError> {
        // Seek to settlement start
        file.seek(SeekFrom::Start(offset))?;

        // Read header
        let header = self.read_header(file)?;

        // Validate
        if header.magic != SSMF_MAGIC {
            return Err(StartupError::InvalidMagic);
        }
        if header.flags & SSMF_FLAG_EXECUTABLE == 0 {
            return Err(StartupError::NotExecutable);
        }

        // Allocate code memory
        let code_mem = self
            .allocator
            .allocate(header.code_size as usize, 4096)
            .map_err(|_| StartupError::MemoryAllocationFailed)?;

        // Allocate data memory
        let data_mem = self
            .allocator
            .allocate(header.data_size as usize, 4096)
            .map_err(|_| StartupError::MemoryAllocationFailed)?;

        // Read code section
        file.seek(SeekFrom::Start(offset + header.code_offset))?;
        let code_slice = unsafe {
            std::slice::from_raw_parts_mut(code_mem.as_mut_ptr(), header.code_size as usize)
        };
        file.read_exact(code_slice)?;

        // Make code executable
        self.allocator
            .protect(&code_mem, Protection::ReadExecute)
            .map_err(|_| StartupError::MemoryAllocationFailed)?;

        // Read data section
        file.seek(SeekFrom::Start(offset + header.data_offset))?;
        let data_slice = unsafe {
            std::slice::from_raw_parts_mut(data_mem.as_mut_ptr(), header.data_size as usize)
        };
        file.read_exact(data_slice)?;

        // Make data read-write
        self.allocator
            .protect(&data_mem, Protection::ReadWrite)
            .map_err(|_| StartupError::MemoryAllocationFailed)?;

        // Read function table with code base for address fixup
        let loaded_code_base = code_mem.as_ptr() as u64;
        let func_table = self.read_function_table(file, offset, &header, loaded_code_base)?;

        // Read global table with data base for address fixup
        let loaded_data_base = data_mem.as_ptr() as u64;
        let global_table = self.read_global_table(file, offset, &header, loaded_data_base)?;

        // Load native libraries
        let native_libs = self.load_native_libs(file, offset, &header)?;

        // Calculate entry point
        let entry_fn = if header.entry_func_idx != u32::MAX {
            func_table
                .get_code_ptr(TableIndex(header.entry_func_idx))
                .map(|p| p as *const u8)
        } else {
            None
        };

        Ok(LoadedSettlement {
            code_mem,
            data_mem,
            func_table,
            global_table,
            native_libs,
            entry_fn,
            _allocator: self.allocator.clone(),
        })
    }

    /// Read the settlement header.
    fn read_header(&self, file: &mut File) -> Result<SettlementHeader, StartupError> {
        let mut buf = [0u8; std::mem::size_of::<SettlementHeader>()];
        file.read_exact(&mut buf)?;

        // Safety: SettlementHeader is repr(C) and contains only primitive types
        let header: SettlementHeader =
            unsafe { std::ptr::read_unaligned(buf.as_ptr() as *const SettlementHeader) };

        Ok(header)
    }

    /// Read and reconstruct the function table.
    ///
    /// The function table in the file contains relative offsets from the code region base.
    /// We convert these to absolute addresses by adding `loaded_code_base`.
    fn read_function_table(
        &self,
        file: &mut File,
        base_offset: u64,
        header: &SettlementHeader,
        loaded_code_base: u64,
    ) -> Result<FunctionTable, StartupError> {
        let mut table = FunctionTable::new();

        if header.func_table_size == 0 {
            return Ok(table);
        }

        file.seek(SeekFrom::Start(base_offset + header.func_table_offset))?;

        let entry_count = header.func_table_size as usize
            / std::mem::size_of::<crate::smf::settlement::FuncTableEntry>();

        for _ in 0..entry_count {
            let mut entry_buf =
                [0u8; std::mem::size_of::<crate::smf::settlement::FuncTableEntry>()];
            file.read_exact(&mut entry_buf)?;

            let entry: crate::smf::settlement::FuncTableEntry =
                unsafe { std::ptr::read_unaligned(entry_buf.as_ptr() as *const _) };

            if entry.is_valid() {
                // Convert relative offset to absolute address
                let absolute_addr = loaded_code_base + entry.code_ptr;
                table.allocate(absolute_addr as usize, entry.module_id, entry.version);
            }
        }

        Ok(table)
    }

    /// Read and reconstruct the global table.
    ///
    /// The global table in the file contains relative offsets from the data region base.
    /// We convert these to absolute addresses by adding `loaded_data_base`.
    fn read_global_table(
        &self,
        file: &mut File,
        base_offset: u64,
        header: &SettlementHeader,
        loaded_data_base: u64,
    ) -> Result<GlobalTable, StartupError> {
        let mut table = GlobalTable::new();

        if header.global_table_size == 0 {
            return Ok(table);
        }

        file.seek(SeekFrom::Start(base_offset + header.global_table_offset))?;

        let entry_count = header.global_table_size as usize
            / std::mem::size_of::<crate::smf::settlement::GlobalTableEntry>();

        for _ in 0..entry_count {
            let mut entry_buf =
                [0u8; std::mem::size_of::<crate::smf::settlement::GlobalTableEntry>()];
            file.read_exact(&mut entry_buf)?;

            let entry: crate::smf::settlement::GlobalTableEntry =
                unsafe { std::ptr::read_unaligned(entry_buf.as_ptr() as *const _) };

            // Convert relative offset to absolute address
            let absolute_addr = loaded_data_base + entry.data_ptr;
            table.allocate(absolute_addr as usize, entry.size, entry.module_id);
        }

        Ok(table)
    }

    /// Load native libraries referenced by the settlement.
    fn load_native_libs(
        &self,
        file: &mut File,
        base_offset: u64,
        header: &SettlementHeader,
    ) -> Result<NativeLibManager, StartupError> {
        let mut manager = NativeLibManager::new();

        if header.native_lib_count == 0 {
            return Ok(manager);
        }

        // Read native lib entries
        file.seek(SeekFrom::Start(base_offset + header.native_libs_offset))?;

        for _ in 0..header.native_lib_count {
            let mut entry_buf = [0u8; std::mem::size_of::<NativeLibEntry>()];
            file.read_exact(&mut entry_buf)?;

            let entry: NativeLibEntry =
                unsafe { std::ptr::read_unaligned(entry_buf.as_ptr() as *const _) };

            // Read library name from string table
            let name = self.read_string(
                file,
                base_offset + header.string_table_offset + entry.name_offset as u64,
            )?;

            match entry.lib_type {
                NATIVE_LIB_SHARED => {
                    // Read path from string table
                    let path = self.read_string(
                        file,
                        base_offset + header.string_table_offset + entry.path_offset as u64,
                    )?;
                    manager
                        .add_shared(&name, Path::new(&path))
                        .map_err(|e| StartupError::NativeLibLoadFailed(e))?;
                }
                NATIVE_LIB_SYSTEM => {
                    manager
                        .add_system(&name)
                        .map_err(|e| StartupError::NativeLibLoadFailed(e))?;
                }
                _ => {
                    // Static libs are embedded - data is in the settlement
                    // For startup loader, we just record the pointer
                    if entry.data_size > 0 {
                        // Calculate where static lib data would be in our loaded memory
                        // For now, skip static libs in startup loader
                    }
                }
            }
        }

        Ok(manager)
    }

    /// Read a null-terminated string from the file.
    fn read_string(&self, file: &mut File, offset: u64) -> Result<String, StartupError> {
        let current_pos = file.stream_position()?;
        file.seek(SeekFrom::Start(offset))?;

        let mut bytes = Vec::new();
        let mut buf = [0u8; 1];

        loop {
            file.read_exact(&mut buf)?;
            if buf[0] == 0 {
                break;
            }
            bytes.push(buf[0]);
        }

        file.seek(SeekFrom::Start(current_pos))?;

        String::from_utf8(bytes).map_err(|_| StartupError::InvalidHeader)
    }
}

impl Default for StartupLoader {
    fn default() -> Self {
        Self::new()
    }
}

/// Main entry point for settlement executables.
///
/// This function is designed to be called from a minimal main() in the
/// executable stub. It loads and executes the settlement.
pub fn settlement_main() -> i32 {
    match StartupLoader::load_from_self() {
        Ok(settlement) => match unsafe { settlement.execute() } {
            Ok(code) => code,
            Err(e) => {
                eprintln!("Execution error: {}", e);
                1
            }
        },
        Err(e) => {
            eprintln!("Load error: {}", e);
            1
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_startup_loader_creation() {
        let loader = StartupLoader::new();
        // Just verify it can be created
        drop(loader);
    }

    #[test]
    fn test_startup_error_display() {
        let e = StartupError::InvalidMagic;
        assert!(e.to_string().contains("Invalid SSMF magic"));

        let e = StartupError::NoEntryPoint;
        assert!(e.to_string().contains("No entry point"));
    }
}
