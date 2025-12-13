//! Settlement builder for creating settlement files and executables.
//!
//! This module provides functionality to serialize settlements to the SSMF format
//! and create standalone executables.

use std::collections::HashMap;
use std::fs::File;
use std::io::{self, Read, Seek, Write};
use std::path::{Path, PathBuf};

use crate::settlement::Settlement;
use crate::smf::settlement::{
    DependencyEntry, FuncTableEntry, GlobalTableEntry, ModuleTableEntry, NativeLibEntry,
    SettlementHeader, TypeTableEntry, SSMF_FLAG_EXECUTABLE, SSMF_FLAG_HAS_NATIVE_LIBS, SSMF_MAGIC,
    SSMF_VERSION,
};

/// Find the simple-stub executable.
/// Looks in several locations:
/// 1. Environment variable SIMPLE_STUB_PATH
/// 2. Same directory as the current executable
/// 3. target/release/simple-stub (for development)
/// 4. target/debug/simple-stub (for development)
pub fn find_stub() -> Option<PathBuf> {
    // Check environment variable first
    if let Ok(path) = std::env::var("SIMPLE_STUB_PATH") {
        let p = PathBuf::from(path);
        if p.exists() {
            return Some(p);
        }
    }

    // Check same directory as current executable
    if let Ok(exe_path) = std::env::current_exe() {
        if let Some(dir) = exe_path.parent() {
            let stub_path = dir.join("simple-stub");
            if stub_path.exists() {
                return Some(stub_path);
            }
            // Windows
            let stub_path = dir.join("simple-stub.exe");
            if stub_path.exists() {
                return Some(stub_path);
            }
        }
    }

    // Check target directories (for development)
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").ok();
    let workspace_root = manifest_dir
        .as_ref()
        .and_then(|d| PathBuf::from(d).parent().map(|p| p.to_path_buf()))
        .or_else(|| std::env::current_dir().ok());

    if let Some(root) = workspace_root {
        // Try release first
        let release_stub = root.join("target/release/simple-stub");
        if release_stub.exists() {
            return Some(release_stub);
        }

        // Try debug
        let debug_stub = root.join("target/debug/simple-stub");
        if debug_stub.exists() {
            return Some(debug_stub);
        }

        // Walk up to find workspace root
        let mut current = root;
        for _ in 0..5 {
            let release_stub = current.join("target/release/simple-stub");
            if release_stub.exists() {
                return Some(release_stub);
            }
            let debug_stub = current.join("target/debug/simple-stub");
            if debug_stub.exists() {
                return Some(debug_stub);
            }
            if let Some(parent) = current.parent() {
                current = parent.to_path_buf();
            } else {
                break;
            }
        }
    }

    None
}

/// Errors that can occur during settlement building.
#[derive(Debug)]
pub enum BuildError {
    IoError(io::Error),
    NoEntryPoint,
    InvalidStub,
    ModuleNotFound(String),
}

impl std::fmt::Display for BuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BuildError::IoError(e) => write!(f, "I/O error: {}", e),
            BuildError::NoEntryPoint => write!(f, "No entry point defined"),
            BuildError::InvalidStub => write!(f, "Invalid executable stub"),
            BuildError::ModuleNotFound(name) => write!(f, "Module not found: {}", name),
        }
    }
}

impl std::error::Error for BuildError {}

impl From<io::Error> for BuildError {
    fn from(e: io::Error) -> Self {
        BuildError::IoError(e)
    }
}

/// Options for building a settlement.
#[derive(Debug, Clone)]
pub struct BuildOptions {
    /// Whether to create an executable
    pub executable: bool,
    /// Path to executable stub (required if executable=true)
    pub stub_path: Option<std::path::PathBuf>,
    /// Target architecture
    pub arch: u8,
    /// Include debug info
    pub debug_info: bool,
    /// Compression level (0 = none, 1-9 = increasing compression)
    pub compression: u8,
}

impl Default for BuildOptions {
    fn default() -> Self {
        Self {
            executable: false,
            stub_path: None,
            arch: Self::current_arch(),
            debug_info: false,
            compression: 0,
        }
    }
}

impl BuildOptions {
    /// Get the architecture code for the current platform.
    pub fn current_arch() -> u8 {
        #[cfg(target_arch = "x86_64")]
        {
            1
        }
        #[cfg(target_arch = "aarch64")]
        {
            2
        }
        #[cfg(target_arch = "x86")]
        {
            3
        }
        #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "x86")))]
        {
            0
        }
    }

    /// Create options for building a standalone executable.
    pub fn executable<P: Into<std::path::PathBuf>>(stub_path: P) -> Self {
        Self {
            executable: true,
            stub_path: Some(stub_path.into()),
            ..Default::default()
        }
    }

    /// Create options for building a settlement file (not executable).
    pub fn settlement_file() -> Self {
        Self {
            executable: false,
            ..Default::default()
        }
    }
}

/// Builder for creating settlement files and executables.
pub struct SettlementBuilder {
    options: BuildOptions,
}

impl SettlementBuilder {
    /// Create a new builder with default options.
    pub fn new() -> Self {
        Self {
            options: BuildOptions::default(),
        }
    }

    /// Create a builder with specific options.
    pub fn with_options(options: BuildOptions) -> Self {
        Self { options }
    }

    /// Build a settlement to a file.
    pub fn build_to_file<P: AsRef<Path>>(
        &self,
        settlement: &Settlement,
        output_path: P,
    ) -> Result<(), BuildError> {
        let mut file = File::create(output_path)?;

        if self.options.executable {
            self.write_executable(settlement, &mut file)?;
        } else {
            self.write_settlement(settlement, &mut file)?;
        }

        Ok(())
    }

    /// Build a settlement to a byte vector.
    pub fn build_to_vec(&self, settlement: &Settlement) -> Result<Vec<u8>, BuildError> {
        let mut buffer = io::Cursor::new(Vec::new());

        if self.options.executable {
            self.write_executable(settlement, &mut buffer)?;
        } else {
            self.write_settlement(settlement, &mut buffer)?;
        }

        Ok(buffer.into_inner())
    }

    /// Write a standalone executable.
    fn write_executable<W: Write + Seek>(
        &self,
        settlement: &Settlement,
        output: &mut W,
    ) -> Result<(), BuildError> {
        // Write executable stub first
        if let Some(stub_path) = &self.options.stub_path {
            let mut stub_file = File::open(stub_path)?;
            let mut stub_data = Vec::new();
            stub_file.read_to_end(&mut stub_data)?;
            output.write_all(&stub_data)?;
        } else {
            // Write a minimal stub that just calls settlement_main
            self.write_minimal_stub(output)?;
        }

        // Record where settlement data starts
        let settlement_offset = output.stream_position()?;

        // Write settlement data
        self.write_settlement(settlement, output)?;

        // Write trailer with offset
        output.write_all(&settlement_offset.to_le_bytes())?;
        output.write_all(b"SSMFOFFS")?;

        Ok(())
    }

    /// Write the settlement data in SSMF format.
    fn write_settlement<W: Write + Seek>(
        &self,
        settlement: &Settlement,
        output: &mut W,
    ) -> Result<(), BuildError> {
        // Build dependency table first (needed for module table)
        let (dep_entries, dep_offsets) = self.build_dependency_table(settlement);

        // Collect all data that needs to be written
        let string_table = self.build_string_table(settlement);
        let code_data = settlement.code_region_slice();
        let data_data = settlement.data_region_slice();
        let func_entries = settlement.func_table_slice();
        let global_entries = settlement.global_table_slice();
        let type_entries = settlement.type_table_slice();
        let module_entries = self.build_module_table(settlement, &string_table, &dep_offsets);
        let native_lib_entries = self.build_native_lib_table(settlement, &string_table);

        // Calculate offsets
        let header_size = std::mem::size_of::<SettlementHeader>() as u64;
        let mut current_offset = header_size;

        // String table comes first after header
        let string_table_offset = current_offset;
        let string_table_data = self.serialize_string_table(&string_table);
        current_offset += string_table_data.len() as u64;

        // Align to 8 bytes
        current_offset = (current_offset + 7) & !7;

        // Code section
        let code_offset = current_offset;
        let code_size = code_data.len() as u64;
        current_offset += code_size;

        // Align to 8 bytes
        current_offset = (current_offset + 7) & !7;

        // Data section
        let data_offset = current_offset;
        let data_size = data_data.len() as u64;
        current_offset += data_size;

        // Align to 8 bytes
        current_offset = (current_offset + 7) & !7;

        // Function table
        let func_table_offset = current_offset;
        let func_table_size = (func_entries.len() * std::mem::size_of::<FuncTableEntry>()) as u64;
        current_offset += func_table_size;

        // Global table
        let global_table_offset = current_offset;
        let global_table_size =
            (global_entries.len() * std::mem::size_of::<GlobalTableEntry>()) as u64;
        current_offset += global_table_size;

        // Type table
        let type_table_offset = current_offset;
        let type_table_size = (type_entries.len() * std::mem::size_of::<TypeTableEntry>()) as u64;
        current_offset += type_table_size;

        // Module table
        let module_table_offset = current_offset;
        let module_table_size =
            (module_entries.len() * std::mem::size_of::<ModuleTableEntry>()) as u64;
        current_offset += module_table_size;

        // Native library table
        let native_libs_offset = current_offset;
        let native_libs_size =
            (native_lib_entries.len() * std::mem::size_of::<NativeLibEntry>()) as u64;
        current_offset += native_libs_size;

        // Dependency table
        let dep_table_offset = current_offset;
        let dep_table_size = (dep_entries.len() * std::mem::size_of::<DependencyEntry>()) as u64;

        // Build flags
        let mut flags = 0u16;
        if self.options.executable {
            flags |= SSMF_FLAG_EXECUTABLE;
        }
        if !native_lib_entries.is_empty() {
            flags |= SSMF_FLAG_HAS_NATIVE_LIBS;
        }

        // Get entry point info
        let (entry_module_idx, entry_func_idx) = settlement.entry_point_indices();

        // Build header
        let header = SettlementHeader {
            magic: SSMF_MAGIC,
            version: SSMF_VERSION,
            flags,
            arch: self.options.arch,
            reserved: [0; 5],
            code_offset,
            code_size,
            data_offset,
            data_size,
            func_table_offset,
            func_table_size,
            global_table_offset,
            global_table_size,
            type_table_offset,
            type_table_size,
            module_table_offset,
            module_table_size,
            native_libs_offset,
            native_libs_size,
            string_table_offset,
            string_table_size: string_table_data.len() as u64,
            dep_table_offset,
            dep_table_size,
            module_count: module_entries.len() as u32,
            native_lib_count: native_lib_entries.len() as u32,
            entry_module_idx,
            entry_func_idx,
            ..Default::default()
        };

        // Write header
        let header_bytes = unsafe {
            std::slice::from_raw_parts(
                &header as *const SettlementHeader as *const u8,
                std::mem::size_of::<SettlementHeader>(),
            )
        };
        output.write_all(header_bytes)?;

        // Write string table
        output.write_all(&string_table_data)?;

        // Pad to alignment
        self.write_padding(
            output,
            string_table_offset + string_table_data.len() as u64,
            code_offset,
        )?;

        // Write code
        output.write_all(code_data)?;

        // Pad to alignment
        self.write_padding(output, code_offset + code_size, data_offset)?;

        // Write data
        output.write_all(data_data)?;

        // Pad to alignment
        self.write_padding(output, data_offset + data_size, func_table_offset)?;

        // Write function table with relative offsets
        // Convert absolute code_ptr to relative offset from code region base
        let code_base = settlement.code_base() as u64;
        for entry in func_entries {
            // Create a copy with relative offset
            let mut rel_entry = *entry;
            if rel_entry.code_ptr != 0 && rel_entry.code_ptr >= code_base {
                rel_entry.code_ptr = rel_entry.code_ptr - code_base;
            }
            let entry_bytes = unsafe {
                std::slice::from_raw_parts(
                    &rel_entry as *const FuncTableEntry as *const u8,
                    std::mem::size_of::<FuncTableEntry>(),
                )
            };
            output.write_all(entry_bytes)?;
        }

        // Write global table with relative offsets
        let data_base = settlement.data_base() as u64;
        for entry in global_entries {
            // Create a copy with relative offset
            let mut rel_entry = *entry;
            if rel_entry.data_ptr != 0 && rel_entry.data_ptr >= data_base {
                rel_entry.data_ptr = rel_entry.data_ptr - data_base;
            }
            let entry_bytes = unsafe {
                std::slice::from_raw_parts(
                    &rel_entry as *const GlobalTableEntry as *const u8,
                    std::mem::size_of::<GlobalTableEntry>(),
                )
            };
            output.write_all(entry_bytes)?;
        }

        // Write type table
        for entry in type_entries {
            let entry_bytes = unsafe {
                std::slice::from_raw_parts(
                    entry as *const TypeTableEntry as *const u8,
                    std::mem::size_of::<TypeTableEntry>(),
                )
            };
            output.write_all(entry_bytes)?;
        }

        // Write module table
        for entry in &module_entries {
            let entry_bytes = unsafe {
                std::slice::from_raw_parts(
                    entry as *const ModuleTableEntry as *const u8,
                    std::mem::size_of::<ModuleTableEntry>(),
                )
            };
            output.write_all(entry_bytes)?;
        }

        // Write native library table
        for entry in &native_lib_entries {
            let entry_bytes = unsafe {
                std::slice::from_raw_parts(
                    entry as *const NativeLibEntry as *const u8,
                    std::mem::size_of::<NativeLibEntry>(),
                )
            };
            output.write_all(entry_bytes)?;
        }

        // Write dependency table
        for entry in &dep_entries {
            let entry_bytes = unsafe {
                std::slice::from_raw_parts(
                    entry as *const DependencyEntry as *const u8,
                    std::mem::size_of::<DependencyEntry>(),
                )
            };
            output.write_all(entry_bytes)?;
        }

        Ok(())
    }

    /// Write padding bytes to align to a target offset.
    fn write_padding<W: Write>(
        &self,
        output: &mut W,
        current: u64,
        target: u64,
    ) -> Result<(), BuildError> {
        if target > current {
            let padding = vec![0u8; (target - current) as usize];
            output.write_all(&padding)?;
        }
        Ok(())
    }

    /// Build the string table from settlement data.
    fn build_string_table(&self, settlement: &Settlement) -> StringTable {
        let mut table = StringTable::new();

        // Add module names
        for module in settlement.iter_modules() {
            table.add(&module.name);
        }

        // Add native library names and paths
        for (_, lib) in settlement.native_libs().iter() {
            table.add(&lib.name);
            // Add path for shared libs if we have it
        }

        table
    }

    /// Serialize the string table to bytes.
    fn serialize_string_table(&self, table: &StringTable) -> Vec<u8> {
        table.data.clone()
    }

    /// Build the module table with dependency offsets.
    fn build_module_table(
        &self,
        settlement: &Settlement,
        strings: &StringTable,
        dep_offsets: &HashMap<String, (u32, u32)>, // module_name -> (dep_start, dep_count)
    ) -> Vec<ModuleTableEntry> {
        settlement
            .iter_modules()
            .map(|module| {
                let (dep_start, dep_count) =
                    dep_offsets.get(&module.name).copied().unwrap_or((0, 0));

                ModuleTableEntry {
                    name_offset: strings.offset(&module.name) as u32,
                    version: module.version,
                    flags: 0,
                    _reserved: 0,
                    code_start: module.code_range.start as u32,
                    code_end: (module.code_range.start + module.code_range.count) as u32,
                    data_start: module.data_range.start as u32,
                    data_end: (module.data_range.start + module.data_range.count) as u32,
                    func_start: module.func_table_range.0 .0,
                    func_count: module.func_table_range.1 as u32,
                    global_start: module.global_table_range.0 .0,
                    global_count: module.global_table_range.1 as u32,
                    type_start: module.type_table_range.0 .0,
                    type_count: module.type_table_range.1 as u32,
                    dep_start,
                    dep_count,
                }
            })
            .collect()
    }

    /// Build the dependency table.
    ///
    /// Returns (dependency_entries, module_dep_offsets)
    /// where module_dep_offsets maps module_name -> (start_index, count)
    fn build_dependency_table(
        &self,
        settlement: &Settlement,
    ) -> (Vec<DependencyEntry>, HashMap<String, (u32, u32)>) {
        let mut entries = Vec::new();
        let mut offsets = HashMap::new();

        for module in settlement.iter_modules() {
            let start = entries.len() as u32;
            let count = module.dependencies.len() as u32;

            for &dep_handle in &module.dependencies {
                // Find the module index (which is the handle value)
                if let Some(dep_module) = settlement.get_module(dep_handle) {
                    entries.push(DependencyEntry {
                        module_idx: dep_handle.0,
                        required_version: dep_module.version,
                    });
                }
            }

            offsets.insert(module.name.clone(), (start, count));
        }

        (entries, offsets)
    }

    /// Build the native library table.
    fn build_native_lib_table(
        &self,
        settlement: &Settlement,
        strings: &StringTable,
    ) -> Vec<NativeLibEntry> {
        settlement
            .native_libs()
            .iter()
            .map(|(_, lib)| {
                NativeLibEntry {
                    name_offset: strings.offset(&lib.name) as u32,
                    lib_type: lib.lib_type,
                    flags: 0,
                    reserved: [0; 2],
                    data_offset: 0, // Would be set for static libs
                    data_size: 0,
                    path_offset: 0, // Would be set for shared libs
                    symbol_count: 0,
                    symbols_offset: 0,
                    _reserved: 0,
                }
            })
            .collect()
    }

    /// Write a minimal executable stub.
    ///
    /// This stub contains the minimum code to:
    /// 1. Find the settlement data appended to itself
    /// 2. Call the startup loader
    /// 3. Execute the entry point
    fn write_minimal_stub<W: Write>(&self, output: &mut W) -> Result<(), BuildError> {
        // Find the stub executable
        let stub_path = find_stub().ok_or(BuildError::InvalidStub)?;

        // Read and write the stub
        let mut stub_file = File::open(&stub_path)?;
        let mut stub_data = Vec::new();
        stub_file.read_to_end(&mut stub_data)?;
        output.write_all(&stub_data)?;

        Ok(())
    }
}

/// Create an executable from a settlement.
///
/// This is a convenience function that:
/// 1. Finds the stub executable
/// 2. Creates a builder with executable options
/// 3. Builds the executable to the output path
pub fn create_executable<P: AsRef<Path>>(
    settlement: &Settlement,
    output_path: P,
) -> Result<(), BuildError> {
    let stub_path = find_stub().ok_or(BuildError::InvalidStub)?;
    let builder = SettlementBuilder::with_options(BuildOptions::executable(stub_path));
    builder.build_to_file(settlement, output_path)
}

impl Default for SettlementBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Helper for building string tables.
struct StringTable {
    data: Vec<u8>,
    offsets: HashMap<String, usize>,
}

impl StringTable {
    fn new() -> Self {
        Self {
            data: Vec::new(),
            offsets: HashMap::new(),
        }
    }

    fn add(&mut self, s: &str) -> usize {
        if let Some(&offset) = self.offsets.get(s) {
            return offset;
        }

        let offset = self.data.len();
        self.data.extend_from_slice(s.as_bytes());
        self.data.push(0); // Null terminator
        self.offsets.insert(s.to_string(), offset);
        offset
    }

    fn offset(&self, s: &str) -> usize {
        self.offsets.get(s).copied().unwrap_or(0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_build_options_default() {
        let opts = BuildOptions::default();
        assert!(!opts.executable);
        assert!(opts.stub_path.is_none());
    }

    #[test]
    fn test_build_options_executable() {
        let opts = BuildOptions::executable("/path/to/stub");
        assert!(opts.executable);
        assert!(opts.stub_path.is_some());
    }

    #[test]
    fn test_string_table() {
        let mut table = StringTable::new();

        let off1 = table.add("hello");
        let off2 = table.add("world");
        let off3 = table.add("hello"); // Duplicate

        assert_eq!(off1, 0);
        assert_eq!(off2, 6); // "hello\0" = 6 bytes
        assert_eq!(off3, off1); // Should reuse

        assert_eq!(table.offset("hello"), 0);
        assert_eq!(table.offset("world"), 6);
        assert_eq!(table.offset("unknown"), 0);
    }

    #[test]
    fn test_builder_creation() {
        let builder = SettlementBuilder::new();
        assert!(!builder.options.executable);

        let builder2 = SettlementBuilder::with_options(BuildOptions::settlement_file());
        assert!(!builder2.options.executable);
    }
}
