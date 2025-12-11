mod loader;
mod module;
mod registry;

// Runtime symbol providers
mod chained_provider;
mod dynamic_provider;
mod provider;
mod static_provider;

pub use loader::{LoadError, ModuleLoader};
pub use module::LoadedModule;
pub use registry::ModuleRegistry;
pub use simple_common::{DynLoader, DynModule};

// Re-export runtime symbol provider types
pub use chained_provider::ChainedProvider;
pub use dynamic_provider::{DynLoadError, DynamicSymbolProvider};
pub use provider::{create_runtime_provider, default_runtime_provider, static_provider, RuntimeLoadMode};
pub use simple_common::{AbiVersion, RuntimeSymbolProvider, RUNTIME_SYMBOL_NAMES};
pub use static_provider::StaticSymbolProvider;
