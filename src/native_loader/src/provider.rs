//! Provider factory and configuration.
//!
//! Provides a unified interface for creating runtime symbol providers
//! with different loading strategies.

use crate::chained_provider::ChainedProvider;
use crate::dynamic_provider::{DynLoadError, DynamicSymbolProvider};
use crate::static_provider::StaticSymbolProvider;
use simple_common::RuntimeSymbolProvider;
use std::path::Path;
use std::sync::Arc;

/// Loading mode for runtime FFI symbols.
///
/// Determines how runtime symbols are resolved at execution time.
#[derive(Clone, Debug)]
pub enum RuntimeLoadMode {
    /// Static linking (compiled into binary).
    ///
    /// Zero runtime lookup cost - all symbols are resolved at compile time.
    /// This is the default for release builds.
    Static,

    /// Dynamic loading from the default system path.
    ///
    /// Loads symbols from the platform-specific default library:
    /// - Linux: `libsimple_runtime.so`
    /// - macOS: `libsimple_runtime.dylib`
    /// - Windows: `simple_runtime.dll`
    Dynamic,

    /// Dynamic loading from a specific path.
    ///
    /// Use this to load a custom runtime library or plugin.
    DynamicPath(String),

    /// Multiple libraries with first-match-wins semantics.
    ///
    /// Providers are tried in order - the first one that has a symbol wins.
    /// Use this for plugin systems where custom libraries can override
    /// or extend the base runtime.
    Chained(Vec<RuntimeLoadMode>),
}

impl Default for RuntimeLoadMode {
    fn default() -> Self {
        Self::Static
    }
}

impl RuntimeLoadMode {
    /// Get the default mode based on the build profile.
    ///
    /// - Debug builds: Try dynamic first, fall back to static
    /// - Release builds: Static only
    ///
    /// This allows debug builds to pick up runtime changes without
    /// recompilation, while release builds get zero-overhead static linking.
    pub fn default_for_profile() -> Self {
        if cfg!(debug_assertions) {
            // Debug: try dynamic first, fall back to static
            Self::Chained(vec![Self::Dynamic, Self::Static])
        } else {
            // Release: static only for performance
            Self::Static
        }
    }

    /// Create a mode that tries multiple paths before falling back to static.
    ///
    /// Useful for development where the runtime library might be in
    /// different locations depending on the build setup.
    pub fn with_fallback_paths(paths: Vec<String>) -> Self {
        let mut modes: Vec<RuntimeLoadMode> = paths
            .into_iter()
            .map(RuntimeLoadMode::DynamicPath)
            .collect();
        modes.push(Self::Dynamic);
        modes.push(Self::Static);
        Self::Chained(modes)
    }
}

/// Create a runtime symbol provider based on the specified mode.
///
/// Returns an `Arc<dyn RuntimeSymbolProvider>` that can be shared
/// across threads and used by the JIT compiler, interpreter, etc.
pub fn create_runtime_provider(
    mode: RuntimeLoadMode,
) -> Result<Arc<dyn RuntimeSymbolProvider>, DynLoadError> {
    match mode {
        RuntimeLoadMode::Static => Ok(Arc::new(StaticSymbolProvider::default())),

        RuntimeLoadMode::Dynamic => Ok(Arc::new(DynamicSymbolProvider::load_default()?)),

        RuntimeLoadMode::DynamicPath(path) => {
            Ok(Arc::new(DynamicSymbolProvider::load(Path::new(&path))?))
        }

        RuntimeLoadMode::Chained(modes) => {
            let mut chained = ChainedProvider::new();

            for mode in modes {
                // Try to load each provider, skip failures
                // This allows graceful fallback when dynamic libraries aren't available
                match create_runtime_provider(mode) {
                    Ok(provider) => chained.add(provider),
                    Err(_) => continue, // Skip failed providers
                }
            }

            if chained.is_empty() {
                return Err(DynLoadError::LoadError(
                    "no providers could be loaded".to_string(),
                ));
            }

            Ok(Arc::new(chained))
        }
    }
}

/// Create the default runtime provider for the current build profile.
///
/// This is a convenience function that:
/// - In debug builds: tries dynamic loading first, falls back to static
/// - In release builds: uses static linking
///
/// If dynamic loading fails in debug builds, it silently falls back to
/// static linking without errors.
pub fn default_runtime_provider() -> Arc<dyn RuntimeSymbolProvider> {
    create_runtime_provider(RuntimeLoadMode::default_for_profile())
        .unwrap_or_else(|_| Arc::new(StaticSymbolProvider::default()))
}

/// Create a static-only provider.
///
/// Always succeeds and has zero runtime lookup cost.
pub fn static_provider() -> Arc<dyn RuntimeSymbolProvider> {
    Arc::new(StaticSymbolProvider::default())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_static_mode() {
        let provider = create_runtime_provider(RuntimeLoadMode::Static).unwrap();
        assert_eq!(provider.name(), "static");
        assert!(provider.get_symbol("rt_array_new").is_some());
    }

    #[test]
    fn test_default_provider() {
        // Should always succeed (falls back to static if dynamic fails)
        let provider = default_runtime_provider();
        assert!(provider.get_symbol("rt_array_new").is_some());
    }

    #[test]
    fn test_static_provider_helper() {
        let provider = static_provider();
        assert_eq!(provider.name(), "static");
    }

    #[test]
    fn test_chained_with_static_fallback() {
        // Even if dynamic loading fails, static should work
        let mode = RuntimeLoadMode::Chained(vec![
            RuntimeLoadMode::DynamicPath("/nonexistent/path.so".to_string()),
            RuntimeLoadMode::Static,
        ]);

        let provider = create_runtime_provider(mode).unwrap();
        assert!(provider.get_symbol("rt_array_new").is_some());
    }

    #[test]
    fn test_default_mode() {
        let mode = RuntimeLoadMode::default();
        match mode {
            RuntimeLoadMode::Static => (),
            _ => panic!("Default should be Static"),
        }
    }
}
