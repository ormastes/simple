//! Settlement container for consolidating multiple SMF modules.
//!
//! The Settlement struct is the core runtime container that manages
//! merged code/data regions, indirection tables, and native libraries.

use std::collections::HashMap;
use std::sync::Arc;

use crate::memory::{ExecutableMemory, MemoryAllocator, Protection};
use crate::module::LoadedModule;
use crate::smf::settlement::{
    SettlementHeader,
    SSMF_FLAG_EXECUTABLE, SSMF_FLAG_HAS_NATIVES, SSMF_FLAG_RELOADABLE,
};

use super::native::{NativeHandle, NativeLibManager, NativeLibSpec};
use super::slots::{SlotAllocator, SlotRange, CODE_SLOT_SIZE, DATA_SLOT_SIZE};
use super::tables::{FunctionTable, GlobalTable, TableIndex, TypeTable};

/// Handle to a module in the settlement.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModuleHandle(pub u32);

impl ModuleHandle {
    pub const INVALID: ModuleHandle = ModuleHandle(u32::MAX);

    pub fn is_valid(&self) -> bool {
        self.0 != u32::MAX
    }

    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }
}

/// Information about a module in the settlement.
#[derive(Debug)]
pub struct SettlementModule {
    /// Module name
    pub name: String,
    /// Handle for this module
    pub handle: ModuleHandle,
    /// Slot range in code region
    pub code_slots: SlotRange,
    /// Slot range in data region
    pub data_slots: SlotRange,
    /// Function table indices for this module's functions
    pub functions: Vec<TableIndex>,
    /// Global table indices for this module's globals
    pub globals: Vec<TableIndex>,
    /// Type table indices for this module's types
    pub types: Vec<TableIndex>,
    /// Dependencies (other module handles)
    pub dependencies: Vec<ModuleHandle>,
    /// Module version
    pub version: u32,
    /// Original code size (before slot alignment)
    pub code_size: usize,
    /// Original data size
    pub data_size: usize,
    /// Code range as slot start and count (for serialization)
    pub code_range: SlotRange,
    /// Data range as slot start and count (for serialization)
    pub data_range: SlotRange,
    /// Function table range (start_idx, count)
    pub func_table_range: (TableIndex, usize),
    /// Global table range (start_idx, count)
    pub global_table_range: (TableIndex, usize),
    /// Type table range (start_idx, count)
    pub type_table_range: (TableIndex, usize),
}

/// Error type for settlement operations.
#[derive(Debug)]
pub enum SettlementError {
    /// Not enough space in code region
    CodeRegionFull,
    /// Not enough space in data region
    DataRegionFull,
    /// Module not found
    ModuleNotFound(String),
    /// Module has dependents, cannot remove
    HasDependents(String, Vec<String>),
    /// Native library error
    NativeLibError(String),
    /// Memory allocation error
    MemoryError(String),
    /// Invalid module
    InvalidModule(String),
    /// Dependency cycle detected
    DependencyCycle(Vec<String>),
}

impl std::fmt::Display for SettlementError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SettlementError::CodeRegionFull => write!(f, "Code region full"),
            SettlementError::DataRegionFull => write!(f, "Data region full"),
            SettlementError::ModuleNotFound(name) => write!(f, "Module not found: {}", name),
            SettlementError::HasDependents(name, deps) => {
                write!(f, "Module {} has dependents: {:?}", name, deps)
            }
            SettlementError::NativeLibError(msg) => write!(f, "Native lib error: {}", msg),
            SettlementError::MemoryError(msg) => write!(f, "Memory error: {}", msg),
            SettlementError::InvalidModule(msg) => write!(f, "Invalid module: {}", msg),
            SettlementError::DependencyCycle(cycle) => {
                write!(f, "Dependency cycle: {:?}", cycle)
            }
        }
    }
}

impl std::error::Error for SettlementError {}

/// Configuration for creating a settlement.
#[derive(Debug, Clone)]
pub struct SettlementConfig {
    /// Size of code region in bytes
    pub code_region_size: usize,
    /// Size of data region in bytes
    pub data_region_size: usize,
    /// Enable hot reload support
    pub reloadable: bool,
    /// Target as executable
    pub executable: bool,
}

impl Default for SettlementConfig {
    fn default() -> Self {
        Self {
            code_region_size: 64 * 1024 * 1024, // 64MB
            data_region_size: 32 * 1024 * 1024, // 32MB
            reloadable: true,
            executable: false,
        }
    }
}

/// The main settlement container.
///
/// Consolidates multiple SMF modules into merged memory regions
/// with indirection tables for function/global access.
pub struct Settlement {
    /// Settlement configuration
    config: SettlementConfig,

    /// Code region memory
    code_region: ExecutableMemory,
    /// Data region memory
    data_region: ExecutableMemory,

    /// Slot allocator for code region
    code_slots: SlotAllocator,
    /// Slot allocator for data region
    data_slots: SlotAllocator,

    /// Function indirection table
    func_table: FunctionTable,
    /// Global indirection table
    global_table: GlobalTable,
    /// Type indirection table
    type_table: TypeTable,

    /// Registered modules
    modules: Vec<SettlementModule>,
    /// Module lookup by name
    modules_by_name: HashMap<String, ModuleHandle>,

    /// Native library manager
    native_libs: NativeLibManager,

    /// Entry module (has main function)
    entry_module: Option<ModuleHandle>,
    /// Entry function index in func_table
    entry_func_idx: Option<TableIndex>,

    /// Memory allocator reference
    allocator: Arc<dyn MemoryAllocator>,
}

// Safety: Settlement manages its own memory and synchronization
unsafe impl Send for Settlement {}
unsafe impl Sync for Settlement {}

impl Settlement {
    /// Create a new settlement with given configuration.
    pub fn new(
        config: SettlementConfig,
        allocator: Arc<dyn MemoryAllocator>,
    ) -> Result<Self, SettlementError> {
        // Allocate code region (page-aligned)
        let code_region = allocator
            .allocate(config.code_region_size, 4096)
            .map_err(|e| SettlementError::MemoryError(e.to_string()))?;

        // Set code region to RWX for now (will be RX after loading)
        allocator
            .protect(&code_region, Protection::ReadWriteExecute)
            .map_err(|e| SettlementError::MemoryError(e.to_string()))?;

        // Allocate data region
        let data_region = allocator
            .allocate(config.data_region_size, 4096)
            .map_err(|e| SettlementError::MemoryError(e.to_string()))?;

        // Set data region to RW
        allocator
            .protect(&data_region, Protection::ReadWrite)
            .map_err(|e| SettlementError::MemoryError(e.to_string()))?;

        let code_ptr = code_region.as_mut_ptr();
        let data_ptr = data_region.as_mut_ptr();

        Ok(Self {
            code_slots: SlotAllocator::new(code_ptr, config.code_region_size, CODE_SLOT_SIZE),
            data_slots: SlotAllocator::new(data_ptr, config.data_region_size, DATA_SLOT_SIZE),
            code_region,
            data_region,
            config,
            func_table: FunctionTable::new(),
            global_table: GlobalTable::new(),
            type_table: TypeTable::new(),
            modules: Vec::new(),
            modules_by_name: HashMap::new(),
            native_libs: NativeLibManager::new(),
            entry_module: None,
            entry_func_idx: None,
            allocator,
        })
    }

    /// Create with default configuration.
    pub fn with_defaults(allocator: Arc<dyn MemoryAllocator>) -> Result<Self, SettlementError> {
        Self::new(SettlementConfig::default(), allocator)
    }

    /// Add a module to the settlement.
    pub fn add_module(&mut self, module: &LoadedModule) -> Result<ModuleHandle, SettlementError> {
        // Use path as module name
        let name = module.path.file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("unknown")
            .to_string();

        // Check if module already exists
        if self.modules_by_name.contains_key(&name) {
            return Err(SettlementError::InvalidModule(format!(
                "Module '{}' already exists",
                name
            )));
        }

        // Get code size from module's code memory
        let code_size = module.code_mem.size();
        let data_size = module.data_mem.as_ref().map(|d| d.size()).unwrap_or(0);

        // Allocate code slots
        let code_slots = self
            .code_slots
            .allocate_bytes(code_size)
            .ok_or(SettlementError::CodeRegionFull)?;

        // Allocate data slots
        let data_slots = if data_size > 0 {
            self.data_slots
                .allocate_bytes(data_size)
                .ok_or(SettlementError::DataRegionFull)?
        } else {
            SlotRange::new(0, 0)
        };

        // Copy code to settlement
        let (code_ptr, _) = self.code_slots.get_memory(code_slots);
        unsafe {
            std::ptr::copy_nonoverlapping(
                module.code_mem.as_ptr(),
                code_ptr,
                code_size,
            );
        }

        // Copy data to settlement
        if let Some(ref data_mem) = module.data_mem {
            let (data_ptr, _) = self.data_slots.get_memory(data_slots);
            unsafe {
                std::ptr::copy_nonoverlapping(
                    data_mem.as_ptr(),
                    data_ptr,
                    data_size,
                );
            }
        }

        // Create module handle
        let handle = ModuleHandle(self.modules.len() as u32);

        // Register functions in function table
        let mut functions = Vec::new();

        // Register entry point if executable
        if module.header.is_executable() {
            let entry_offset = module.header.entry_point as usize;
            let settlement_addr = code_ptr as usize + entry_offset;

            let func_idx = self.func_table.allocate(settlement_addr, handle.0 as u16, 1);
            functions.push(func_idx);

            // If this is the first module with entry, set it as entry module
            if self.entry_module.is_none() {
                self.entry_module = Some(handle);
                self.entry_func_idx = Some(func_idx);
            }
        }

        // Register exports in function table
        let module_code_base = module.code_mem.as_ptr() as usize;
        for sym in module.symbols.exports() {
            if sym.sym_type == crate::smf::SymbolType::Function {
                let offset = sym.value as usize;
                let settlement_addr = code_ptr as usize + offset;
                let func_idx = self.func_table.allocate(settlement_addr, handle.0 as u16, 1);
                functions.push(func_idx);
            }
        }

        // Calculate table ranges
        let func_start = if functions.is_empty() {
            TableIndex::INVALID
        } else {
            functions[0]
        };

        // Create settlement module entry
        let settlement_module = SettlementModule {
            name: name.clone(),
            handle,
            code_slots,
            data_slots,
            functions: functions.clone(),
            globals: Vec::new(), // TODO: populate from module
            types: Vec::new(),   // TODO: populate from module
            dependencies: Vec::new(), // TODO: resolve dependencies
            version: module.version,
            code_size,
            data_size,
            code_range: code_slots,
            data_range: data_slots,
            func_table_range: (func_start, functions.len()),
            global_table_range: (TableIndex::INVALID, 0),
            type_table_range: (TableIndex::INVALID, 0),
        };

        self.modules.push(settlement_module);
        self.modules_by_name.insert(name, handle);

        Ok(handle)
    }

    /// Remove a module from the settlement.
    pub fn remove_module(&mut self, handle: ModuleHandle) -> Result<(), SettlementError> {
        let module = self
            .modules
            .get(handle.as_usize())
            .ok_or_else(|| SettlementError::ModuleNotFound(format!("Handle {:?}", handle)))?;

        let name = module.name.clone();

        // Check for dependents
        let dependents: Vec<String> = self
            .modules
            .iter()
            .filter(|m| m.dependencies.contains(&handle))
            .map(|m| m.name.clone())
            .collect();

        if !dependents.is_empty() {
            return Err(SettlementError::HasDependents(name, dependents));
        }

        // Free function table entries
        for &func_idx in &module.functions {
            self.func_table.mark_tombstone(func_idx);
        }

        // Free global table entries
        for &global_idx in &module.globals {
            self.global_table.free(global_idx);
        }

        // Free type table entries
        for &type_idx in &module.types {
            self.type_table.free(type_idx);
        }

        // Free code slots
        self.code_slots.free(module.code_slots);

        // Free data slots
        if module.data_slots.count > 0 {
            self.data_slots.free(module.data_slots);
        }

        // Remove from name lookup
        self.modules_by_name.remove(&name);

        // Mark module as removed (we don't actually remove from Vec to keep handles stable)
        // In a production implementation, you'd want a more sophisticated approach

        Ok(())
    }

    /// Get a module by handle.
    pub fn get_module(&self, handle: ModuleHandle) -> Option<&SettlementModule> {
        if handle.is_valid() {
            self.modules.get(handle.as_usize())
        } else {
            None
        }
    }

    /// Get a module by name.
    pub fn get_module_by_name(&self, name: &str) -> Option<&SettlementModule> {
        self.modules_by_name
            .get(name)
            .and_then(|h| self.get_module(*h))
    }

    /// Add a native library to the settlement.
    pub fn add_native_lib(&mut self, spec: NativeLibSpec) -> Result<NativeHandle, SettlementError> {
        match spec {
            NativeLibSpec::Static { name, data, .. } => {
                // Allocate space in data region for static lib
                let slots = self
                    .data_slots
                    .allocate_bytes(data.len())
                    .ok_or(SettlementError::DataRegionFull)?;

                let (ptr, _) = self.data_slots.get_memory(slots);
                unsafe {
                    std::ptr::copy_nonoverlapping(data.as_ptr(), ptr, data.len());
                }

                Ok(self.native_libs.add_static(&name, ptr, data.len()))
            }
            NativeLibSpec::Shared { name, path } => self
                .native_libs
                .add_shared(&name, &path)
                .map_err(SettlementError::NativeLibError),
            NativeLibSpec::System { name } => self
                .native_libs
                .add_system(&name)
                .map_err(SettlementError::NativeLibError),
        }
    }

    /// Resolve a native symbol.
    pub fn resolve_native_symbol(&mut self, name: &str) -> Option<usize> {
        self.native_libs.resolve_symbol(name)
    }

    /// Get the entry point address.
    pub fn entry_point(&self) -> Option<usize> {
        self.entry_func_idx
            .and_then(|idx| self.func_table.get_code_ptr(idx))
    }

    /// Get function pointer by table index.
    pub fn get_function(&self, idx: TableIndex) -> Option<usize> {
        self.func_table.get_code_ptr(idx)
    }

    /// Get global pointer by table index.
    pub fn get_global(&self, idx: TableIndex) -> Option<usize> {
        self.global_table.get_data_ptr(idx)
    }

    /// Get code region base address.
    pub fn code_base(&self) -> *const u8 {
        self.code_region.as_ptr()
    }

    /// Get data region base address.
    pub fn data_base(&self) -> *const u8 {
        self.data_region.as_ptr()
    }

    /// Get number of modules.
    pub fn module_count(&self) -> usize {
        self.modules.len()
    }

    /// Get number of functions in table.
    pub fn function_count(&self) -> usize {
        self.func_table.len()
    }

    /// Get number of globals in table.
    pub fn global_count(&self) -> usize {
        self.global_table.len()
    }

    /// Get number of native libraries.
    pub fn native_lib_count(&self) -> usize {
        self.native_libs.len()
    }

    /// Check if settlement supports hot reload.
    pub fn is_reloadable(&self) -> bool {
        self.config.reloadable
    }

    /// Check if settlement is configured as executable.
    pub fn is_executable(&self) -> bool {
        self.config.executable
    }

    /// Calculate fragmentation of code region.
    pub fn code_fragmentation(&self) -> f64 {
        self.code_slots.fragmentation()
    }

    /// Calculate fragmentation of data region.
    pub fn data_fragmentation(&self) -> f64 {
        self.data_slots.fragmentation()
    }

    /// Compact the settlement (defragment memory regions).
    ///
    /// This is an expensive operation that moves code/data and updates tables.
    pub fn compact(&mut self) -> Result<(), SettlementError> {
        // Get defragmentation plans
        let code_moves = self.code_slots.defragment_plan();
        let data_moves = self.data_slots.defragment_plan();

        // Move code (need to update function table pointers)
        for (old_range, new_range) in &code_moves {
            let (old_ptr, size) = self.code_slots.get_memory(*old_range);
            let (new_ptr, _) = self.code_slots.get_memory(*new_range);

            // Move the data
            unsafe {
                std::ptr::copy(old_ptr, new_ptr, size);
            }

            // Update function table entries that point to this range
            let old_base = old_ptr as usize;
            let new_base = new_ptr as usize;
            let delta = new_base as isize - old_base as isize;

            for (idx, entry) in self.func_table.iter_valid() {
                let ptr = entry.code_ptr as usize;
                if ptr >= old_base && ptr < old_base + size {
                    let new_ptr = (ptr as isize + delta) as usize;
                    unsafe {
                        self.func_table.update_code_ptr(idx, new_ptr);
                    }
                }
            }
        }

        // Move data (need to update global table pointers)
        for (old_range, new_range) in &data_moves {
            let (old_ptr, size) = self.data_slots.get_memory(*old_range);
            let (new_ptr, _) = self.data_slots.get_memory(*new_range);

            unsafe {
                std::ptr::copy(old_ptr, new_ptr, size);
            }

            // Update global table entries
            let old_base = old_ptr as usize;
            let new_base = new_ptr as usize;
            let delta = new_base as isize - old_base as isize;

            for idx in 0..self.global_table.len() {
                let idx = TableIndex(idx as u32);
                if let Some(ptr) = self.global_table.get_data_ptr(idx) {
                    if ptr >= old_base && ptr < old_base + size {
                        let new_ptr = (ptr as isize + delta) as usize;
                        unsafe {
                            self.global_table.update_data_ptr(idx, new_ptr);
                        }
                    }
                }
            }
        }

        // Apply changes to slot allocators
        self.code_slots.apply_defragment(&code_moves);
        self.data_slots.apply_defragment(&data_moves);

        Ok(())
    }

    /// Generate settlement header for serialization.
    pub fn to_header(&self) -> SettlementHeader {
        let mut header = SettlementHeader::new();

        header.flags = 0;
        if self.config.executable {
            header.flags |= SSMF_FLAG_EXECUTABLE;
        }
        if self.config.reloadable {
            header.flags |= SSMF_FLAG_RELOADABLE;
        }
        if !self.native_libs.is_empty() {
            header.flags |= SSMF_FLAG_HAS_NATIVES;
        }

        header.module_count = self.modules.len() as u32;
        header.native_lib_count = self.native_libs.len() as u32;
        header.func_table_count = self.func_table.len() as u32;
        header.global_table_count = self.global_table.len() as u32;
        header.type_table_count = self.type_table.len() as u32;

        if let Some(entry_module) = self.entry_module {
            header.entry_module_idx = entry_module.0;
        }
        if let Some(entry_func) = self.entry_func_idx {
            header.entry_func_idx = entry_func.0;
        }

        header
    }

    /// Iterate over all modules.
    pub fn modules(&self) -> impl Iterator<Item = &SettlementModule> {
        self.modules.iter()
    }

    // ============== Serialization helpers for SettlementBuilder ==============

    /// Get code region as byte slice.
    pub fn code_region_slice(&self) -> &[u8] {
        unsafe {
            std::slice::from_raw_parts(
                self.code_region.as_ptr(),
                self.code_region.size(),
            )
        }
    }

    /// Get data region as byte slice.
    pub fn data_region_slice(&self) -> &[u8] {
        unsafe {
            std::slice::from_raw_parts(
                self.data_region.as_ptr(),
                self.data_region.size(),
            )
        }
    }

    /// Get function table entries as slice.
    pub fn func_table_slice(&self) -> &[crate::smf::settlement::FuncTableEntry] {
        self.func_table.as_slice()
    }

    /// Get global table entries as slice.
    pub fn global_table_slice(&self) -> &[crate::smf::settlement::GlobalTableEntry] {
        self.global_table.as_slice()
    }

    /// Get type table entries as slice.
    pub fn type_table_slice(&self) -> &[crate::smf::settlement::TypeTableEntry] {
        self.type_table.as_slice()
    }

    /// Iterate over modules with serialization info.
    pub fn iter_modules(&self) -> impl Iterator<Item = &SettlementModule> {
        self.modules.iter()
    }

    /// Get native library manager reference.
    pub fn native_libs(&self) -> &NativeLibManager {
        &self.native_libs
    }

    /// Get entry point indices for serialization.
    /// Returns (entry_module_idx, entry_func_idx).
    pub fn entry_point_indices(&self) -> (u32, u32) {
        let module_idx = self.entry_module.map(|h| h.0).unwrap_or(u32::MAX);
        let func_idx = self.entry_func_idx.map(|i| i.0).unwrap_or(u32::MAX);
        (module_idx, func_idx)
    }
}

impl Drop for Settlement {
    fn drop(&mut self) {
        // Note: We cannot move out of self in Drop, so we use std::mem::take
        // to get ownership of the ExecutableMemory regions
        let code_region = std::mem::replace(
            &mut self.code_region,
            ExecutableMemory { ptr: std::ptr::null_mut(), size: 0 },
        );
        let data_region = std::mem::replace(
            &mut self.data_region,
            ExecutableMemory { ptr: std::ptr::null_mut(), size: 0 },
        );

        // Free allocated memory regions
        if !code_region.ptr.is_null() {
            let _ = self.allocator.free(code_region);
        }
        if !data_region.ptr.is_null() {
            let _ = self.allocator.free(data_region);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Mock allocator for testing
    struct MockAllocator;

    impl MemoryAllocator for MockAllocator {
        fn allocate(&self, size: usize, _alignment: usize) -> std::io::Result<ExecutableMemory> {
            let layout = std::alloc::Layout::from_size_align(size, 4096).unwrap();
            let ptr = unsafe { std::alloc::alloc(layout) };
            if ptr.is_null() {
                Err(std::io::Error::new(std::io::ErrorKind::OutOfMemory, "Allocation failed"))
            } else {
                Ok(ExecutableMemory { ptr, size })
            }
        }

        fn protect(&self, _mem: &ExecutableMemory, _prot: Protection) -> std::io::Result<()> {
            Ok(())
        }

        fn free(&self, mem: ExecutableMemory) -> std::io::Result<()> {
            let layout = std::alloc::Layout::from_size_align(mem.size, 4096).unwrap();
            unsafe { std::alloc::dealloc(mem.ptr, layout) };
            Ok(())
        }
    }

    #[test]
    fn test_settlement_creation() {
        let allocator = Arc::new(MockAllocator);
        let config = SettlementConfig {
            code_region_size: 1024 * 1024, // 1MB
            data_region_size: 512 * 1024,  // 512KB
            reloadable: true,
            executable: false,
        };

        let settlement = Settlement::new(config, allocator).unwrap();
        assert_eq!(settlement.module_count(), 0);
        assert!(settlement.is_reloadable());
        assert!(!settlement.is_executable());
    }

    #[test]
    fn test_module_handle() {
        let h = ModuleHandle(5);
        assert!(h.is_valid());
        assert_eq!(h.as_usize(), 5);
        assert!(!ModuleHandle::INVALID.is_valid());
    }

    #[test]
    fn test_settlement_header() {
        let allocator = Arc::new(MockAllocator);
        let config = SettlementConfig {
            code_region_size: 1024 * 1024,
            data_region_size: 512 * 1024,
            reloadable: true,
            executable: true,
        };

        let settlement = Settlement::new(config, allocator).unwrap();
        let header = settlement.to_header();

        assert!(header.is_valid());
        assert!(header.is_executable());
        assert!(header.is_reloadable());
    }
}
