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
    /// Always uses static linking to avoid TLS split-brain issues where
    /// the capture start/stop functions set TLS in the static copy while
    /// the print functions check TLS in the dynamic copy.
    ///
    /// Previously, debug builds tried dynamic loading first, but this
    /// caused output capture to fail in JIT-compiled code.
    pub fn default_for_profile() -> Self {
        if let Ok(path) = std::env::var("SIMPLE_RUNTIME_PATH") {
            let trimmed = path.trim();
            if !trimmed.is_empty() {
                return Self::DynamicPath(trimmed.to_string());
            }
        }

        if let Ok(mode) = std::env::var("SIMPLE_RUNTIME_LOAD") {
            match mode.trim().to_ascii_lowercase().as_str() {
                "dynamic" => return Self::Dynamic,
                "static" => return Self::Static,
                _ => {}
            }
        }

        // Default to static linking to ensure TLS consistency
        // between capture functions and print functions.
        Self::Static
    }

    /// Create a mode that tries multiple paths before falling back to static.
    ///
    /// Useful for development where the runtime library might be in
    /// different locations depending on the build setup.
    pub fn with_fallback_paths(paths: Vec<String>) -> Self {
        let mut modes: Vec<RuntimeLoadMode> = paths.into_iter().map(RuntimeLoadMode::DynamicPath).collect();
        modes.push(Self::Dynamic);
        modes.push(Self::Static);
        Self::Chained(modes)
    }
}

/// Create a runtime symbol provider based on the specified mode.
///
/// Returns an `Arc<dyn RuntimeSymbolProvider>` that can be shared
/// across threads and used by the JIT compiler, interpreter, etc.
pub fn create_runtime_provider(mode: RuntimeLoadMode) -> Result<Arc<dyn RuntimeSymbolProvider>, DynLoadError> {
    match mode {
        RuntimeLoadMode::Static => Ok(Arc::new(StaticSymbolProvider::default())),

        RuntimeLoadMode::Dynamic => Ok(Arc::new(DynamicSymbolProvider::load_default()?)),

        RuntimeLoadMode::DynamicPath(path) => Ok(Arc::new(DynamicSymbolProvider::load(Path::new(&path))?)),

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
                return Err(DynLoadError::LoadError("no providers could be loaded".to_string()));
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
    let mode = RuntimeLoadMode::default_for_profile();
    create_runtime_provider(mode.clone()).unwrap_or_else(|err| {
        eprintln!(
            "warning: failed to initialize runtime provider {:?}: {}; falling back to static",
            mode, err
        );
        Arc::new(StaticSymbolProvider::default())
    })
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
    use std::sync::Mutex;

    static ENV_MUTEX: Mutex<()> = Mutex::new(());

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

    #[test]
    fn test_default_for_profile_honors_runtime_path() {
        let _guard = ENV_MUTEX.lock().unwrap();
        std::env::set_var("SIMPLE_RUNTIME_PATH", "/tmp/libsimple_runtime.so");
        std::env::remove_var("SIMPLE_RUNTIME_LOAD");
        match RuntimeLoadMode::default_for_profile() {
            RuntimeLoadMode::DynamicPath(path) => assert_eq!(path, "/tmp/libsimple_runtime.so"),
            other => panic!("expected DynamicPath, got {:?}", other),
        }
        std::env::remove_var("SIMPLE_RUNTIME_PATH");
    }

    #[test]
    fn test_default_for_profile_honors_runtime_load_mode() {
        let _guard = ENV_MUTEX.lock().unwrap();
        std::env::remove_var("SIMPLE_RUNTIME_PATH");
        std::env::set_var("SIMPLE_RUNTIME_LOAD", "dynamic");
        match RuntimeLoadMode::default_for_profile() {
            RuntimeLoadMode::Dynamic => (),
            other => panic!("expected Dynamic, got {:?}", other),
        }
        std::env::remove_var("SIMPLE_RUNTIME_LOAD");
    }
}
