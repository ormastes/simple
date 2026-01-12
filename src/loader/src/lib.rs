// Allow warnings for FFI code and incomplete features
#![allow(clippy::missing_safety_doc)]
#![allow(clippy::fn_to_numeric_cast)]
#![allow(clippy::fn_to_numeric_cast_with_truncation)]
#![allow(dead_code)]

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
//! ## From Memory
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
//! │  │ (from file)     │    │ (from memory)           │  │
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

pub mod arch_validate;
pub mod cross_test;
pub mod loader;
pub mod memory;
pub mod module;
pub mod native_cross;
pub mod package;
pub mod registry;
pub mod settlement;
pub mod smf;
pub mod startup;

pub use loader::{LoadError, ModuleLoader};
pub use module::LoadedModule;
pub use package::{
    extract_resource, list_resources, LoadedPackage, ManifestSection, PackageError, PackageOptions,
    PackageReader, PackageTrailer, PackageWriter, ResourceEntry, SPK_MAGIC, SPK_VERSION,
};
pub use registry::ModuleRegistry;
pub use settlement::{
    create_executable, find_stub, BuildError, BuildOptions, ExportedSymbol, FunctionTable,
    GlobalTable, ImportedSymbol, LinkResult, ModuleHandle, NativeHandle, NativeLibManager,
    NativeLibSpec, Settlement, SettlementBuilder, SettlementConfig, SettlementError,
    SettlementLinker, SettlementModule, SlotAllocator, SlotRange, TableIndex, TypeTable,
};
pub use simple_common::{DynLoader, DynModule};
pub use startup::{settlement_main, LoadedSettlement, StartupError, StartupLoader};

// Multi-architecture support
pub use arch_validate::{
    is_compatible, is_native, native_target, supported_compile_targets, supported_execute_targets,
    ArchValidator, ValidationError, ValidationResult, ValidationWarning,
};
pub use cross_test::{CiConfig, CrossTestResults, TargetFixture, TestMatrix, TestOutcome};
pub use native_cross::{
    build_for_targets, CrossCompileError, NativeLibBuilder, NativeLibConfig, Toolchain,
    ToolchainRegistry,
};
