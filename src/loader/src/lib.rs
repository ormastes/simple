//! SMF (Simple Module Format) loader.
//!
//! This crate provides functionality to load and execute SMF binary modules.
//!
//! # Loading Methods
//!
//! The loader supports two loading methods:
//!
//! ## From File
//! ```ignore
//! let loader = ModuleLoader::new();
//! let module = loader.load(Path::new("program.smf"))?;
//! ```
//!
//! ## From Memory (TODO)
//! ```ignore
//! let loader = ModuleLoader::new();
//! let bytes: Vec<u8> = compile_to_memory(source)?;
//! let module = loader.load_from_memory(&bytes)?;
//! ```
//!
//! # Architecture
//!
//! ```text
//! ┌──────────────────────────────────────────────────────┐
//! │                    ModuleLoader                       │
//! │  ┌─────────────────┐    ┌─────────────────────────┐  │
//! │  │ load(path)      │    │ load_from_memory(bytes) │  │
//! │  │ (from file)     │    │ (from memory) [TODO]    │  │
//! │  └────────┬────────┘    └───────────┬─────────────┘  │
//! │           │                         │                │
//! │           └──────────┬──────────────┘                │
//! │                      ▼                               │
//! │           ┌─────────────────────┐                    │
//! │           │  Internal Loading   │                    │
//! │           │  - Parse header     │                    │
//! │           │  - Read sections    │                    │
//! │           │  - Allocate memory  │                    │
//! │           │  - Apply relocs     │                    │
//! │           └──────────┬──────────┘                    │
//! │                      ▼                               │
//! │           ┌─────────────────────┐                    │
//! │           │   LoadedModule      │                    │
//! │           │  - entry_point()    │                    │
//! │           │  - get_function()   │                    │
//! │           └─────────────────────┘                    │
//! └──────────────────────────────────────────────────────┘
//! ```

pub mod loader;
pub mod memory;
pub mod module;
pub mod registry;
pub mod settlement;
pub mod smf;
pub mod startup;

pub use loader::{LoadError, ModuleLoader};
pub use module::LoadedModule;
pub use registry::ModuleRegistry;
pub use settlement::{
    BuildError, BuildOptions, ModuleHandle, NativeHandle, NativeLibManager, NativeLibSpec,
    Settlement, SettlementBuilder, SettlementConfig, SettlementError, SettlementModule,
    SlotAllocator, SlotRange, FunctionTable, GlobalTable, TypeTable, TableIndex,
    create_executable, find_stub,
};
pub use simple_common::{DynLoader, DynModule};
pub use startup::{LoadedSettlement, StartupError, StartupLoader, settlement_main};
