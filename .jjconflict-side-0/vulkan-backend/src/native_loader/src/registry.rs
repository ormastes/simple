use crate::loader::ModuleLoader;

/// Registry for native modules with caching.
/// This is a type alias for the generic ModuleRegistry from simple_common.
pub type ModuleRegistry = simple_common::ModuleRegistry<ModuleLoader>;
