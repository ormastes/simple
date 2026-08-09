//! Settlement container for consolidating multiple SMF modules.
//!
//! The Settlement struct is the core runtime container that manages
//! merged code/data regions, indirection tables, and native libraries.

use std::collections::HashMap;
use std::sync::Arc;

use super::super::memory::{ExecutableMemory, MemoryAllocator, Protection};
use super::super::module::LoadedModule;
use super::super::smf::settlement::{SettlementHeader, SSMF_FLAG_EXECUTABLE, SSMF_FLAG_HAS_NATIVES, SSMF_FLAG_RELOADABLE};

use super::linker::SettlementLinker;
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

    /// Cross-module linker
    linker: SettlementLinker,

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

include!("container_impl.rs");

impl Drop for Settlement {
    fn drop(&mut self) {
        // Note: We cannot move out of self in Drop, so we use std::mem::take
        // to get ownership of the ExecutableMemory regions
        let code_region = std::mem::replace(
            &mut self.code_region,
            ExecutableMemory {
                ptr: std::ptr::null_mut(),
                size: 0,
                dealloc: |_, _| {},
            },
        );
        let data_region = std::mem::replace(
            &mut self.data_region,
            ExecutableMemory {
                ptr: std::ptr::null_mut(),
                size: 0,
                dealloc: |_, _| {},
            },
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
#[path = "container_tests.rs"]
mod tests;
