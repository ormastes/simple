//! Dynamic symbol provider - loads runtime functions from shared libraries.
//!
//! Supports loading from .so (Linux), .dylib (macOS), and .dll (Windows).
//! Includes ABI version checking and symbol caching.

use libloading::{Library, Symbol};
use simple_simd::{active_simd_tier, SimdTier};
use simple_runtime_abi::{AbiVersion, RUNTIME_SYMBOL_NAMES, RuntimeSymbolProvider};
use std::cell::RefCell;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use thiserror::Error;

/// Error type for dynamic library loading.
#[derive(Debug, Error)]
pub enum DynLoadError {
    /// Library file not found at the specified path.
    #[error("library not found: {0}")]
    LibraryNotFound(PathBuf),

    /// Required symbol not found in the library.
    #[error("symbol not found: {0}")]
    SymbolNotFound(String),

    /// ABI version mismatch between library and expected version.
    #[error("ABI version mismatch: expected {expected}, found {found}")]
    AbiMismatch { expected: AbiVersion, found: AbiVersion },

    /// Generic loading error from libloading.
    #[error("load error: {0}")]
    LoadError(String),
}

/// Provides runtime symbols via dynamic library loading.
///
/// Loads symbols from a shared library (.so/.dylib/.dll) at runtime.
/// Includes ABI version checking and lazy symbol caching for performance.
pub struct DynamicSymbolProvider {
    /// The loaded library handle.
    library: Library,
    /// Path to the loaded library.
    path: PathBuf,
    /// Cache of resolved symbols for performance.
    cache: RefCell<HashMap<String, *const u8>>,
    /// ABI version read from the library.
    abi_version: AbiVersion,
}

// Safety: Library handles from libloading are safe to send between threads.
// The cache uses RefCell for interior mutability within single-threaded access.
// For multi-threaded use, callers should wrap in Arc<Mutex<>> if needed.
unsafe impl Send for DynamicSymbolProvider {}
unsafe impl Sync for DynamicSymbolProvider {}

impl DynamicSymbolProvider {
    /// Load a runtime library from the specified path with ABI version checking.
    ///
    /// The library must export a `simple_runtime_abi_version` function that
    /// returns a u32 encoding the ABI version (major << 16 | minor).
    pub fn load(path: &Path) -> Result<Self, DynLoadError> {
        if Self::uses_default_runtime_name(path) {
            let mut missing_error = None;
            for candidate in Self::runtime_library_candidates(path, active_simd_tier()) {
                match Self::load_exact(&candidate) {
                    Ok(provider) => return Ok(provider),
                    Err(DynLoadError::LibraryNotFound(_)) => {
                        missing_error = Some(DynLoadError::LibraryNotFound(candidate));
                    }
                    Err(err) => return Err(err),
                }
            }

            return Err(missing_error.unwrap_or_else(|| DynLoadError::LibraryNotFound(path.to_path_buf())));
        }

        Self::load_exact(path)
    }

    fn load_exact(path: &Path) -> Result<Self, DynLoadError> {
        let library = unsafe {
            Library::new(path).map_err(|e| {
                if path.exists() {
                    DynLoadError::LoadError(e.to_string())
                } else {
                    DynLoadError::LibraryNotFound(path.to_path_buf())
                }
            })?
        };

        // Read ABI version from library
        let abi_version = unsafe {
            let version_fn: Symbol<extern "C" fn() -> u32> = library
                .get(b"simple_runtime_abi_version")
                .map_err(|_| DynLoadError::SymbolNotFound("simple_runtime_abi_version".to_string()))?;
            AbiVersion::from_u32(version_fn())
        };

        // Verify ABI compatibility
        if !abi_version.is_compatible_with(&AbiVersion::CURRENT) {
            return Err(DynLoadError::AbiMismatch {
                expected: AbiVersion::CURRENT,
                found: abi_version,
            });
        }

        Ok(Self {
            library,
            path: path.to_path_buf(),
            cache: RefCell::new(HashMap::new()),
            abi_version,
        })
    }

    /// Load the runtime library from the default system path.
    ///
    /// Platform-specific defaults:
    /// - Linux: `libsimple_runtime.so`
    /// - macOS: `libsimple_runtime.dylib`
    /// - Windows: `simple_runtime.dll`
    pub fn load_default() -> Result<Self, DynLoadError> {
        Self::load(Path::new(Self::default_library_name()))
    }

    fn uses_default_runtime_name(path: &Path) -> bool {
        path.file_name()
            .and_then(|value| value.to_str())
            .map(|value| value == Self::default_library_name())
            .unwrap_or(false)
    }

    fn runtime_library_candidates(path: &Path, simd_tier: SimdTier) -> Vec<PathBuf> {
        let mut candidates = Vec::new();
        let parent = path.parent().unwrap_or_else(|| Path::new("."));
        for variant in Self::runtime_variant_tiers(simd_tier) {
            candidates.push(parent.join(Self::variant_library_name(variant)));
        }
        candidates.push(path.to_path_buf());
        candidates
    }

    fn runtime_variant_tiers(simd_tier: SimdTier) -> Vec<SimdTier> {
        let mut variants = Vec::new();
        for fallback in simd_tier.best_available_implementation().compatible_fallbacks() {
            if let Some(runtime_variant) = Self::dynamic_runtime_variant(*fallback) {
                if !variants.contains(&runtime_variant) {
                    variants.push(runtime_variant);
                }
            }
        }
        variants
    }

    fn dynamic_runtime_variant(simd_tier: SimdTier) -> Option<SimdTier> {
        match simd_tier.best_available_implementation() {
            SimdTier::X86_64Avx2 => Some(SimdTier::X86_64Avx2),
            SimdTier::X86_64Sse2 => Some(SimdTier::X86_64Sse2),
            SimdTier::Aarch64Neon => Some(SimdTier::Aarch64Neon),
            SimdTier::Riscv64Rvv => Some(SimdTier::Riscv64Rvv),
            _ => None,
        }
    }

    #[cfg(target_os = "linux")]
    fn variant_library_name(simd_tier: SimdTier) -> String {
        format!("libsimple_runtime.{}.so", simd_tier.as_str())
    }

    #[cfg(target_os = "macos")]
    fn variant_library_name(simd_tier: SimdTier) -> String {
        format!("libsimple_runtime.{}.dylib", simd_tier.as_str())
    }

    #[cfg(target_os = "windows")]
    fn variant_library_name(simd_tier: SimdTier) -> String {
        format!("simple_runtime.{}.dll", simd_tier.as_str())
    }

    #[cfg(not(any(target_os = "linux", target_os = "macos", target_os = "windows")))]
    fn variant_library_name(simd_tier: SimdTier) -> String {
        format!("libsimple_runtime.{}.so", simd_tier.as_str())
    }

    /// Get the default library name for the current platform.
    #[cfg(target_os = "linux")]
    pub fn default_library_name() -> &'static str {
        "libsimple_runtime.so"
    }

    #[cfg(target_os = "macos")]
    pub fn default_library_name() -> &'static str {
        "libsimple_runtime.dylib"
    }

    #[cfg(target_os = "windows")]
    pub fn default_library_name() -> &'static str {
        "simple_runtime.dll"
    }

    #[cfg(not(any(target_os = "linux", target_os = "macos", target_os = "windows")))]
    pub fn default_library_name() -> &'static str {
        "libsimple_runtime.so" // Fallback to Linux convention
    }

    /// Get the path to the loaded library.
    pub fn library_path(&self) -> &Path {
        &self.path
    }

    /// Clear the symbol cache (useful for testing).
    pub fn clear_cache(&self) {
        self.cache.borrow_mut().clear();
    }
}

impl RuntimeSymbolProvider for DynamicSymbolProvider {
    fn get_symbol(&self, name: &str) -> Option<*const u8> {
        let normalized = name.strip_prefix('_').unwrap_or(name);
        // Check cache first
        if let Some(&ptr) = self.cache.borrow().get(normalized) {
            return Some(ptr);
        }

        // Load symbol from library.
        //
        // Runtime symbols are exported C functions. Requesting them as `*const u8`
        // from libloading is incorrect because that interprets the symbol as a data
        // symbol and dereferences the bytes at the function entry address. Resolve
        // them as function pointers first, then cast the function address.
        let ptr = unsafe {
            let sym: Symbol<unsafe extern "C" fn()> = self.library.get(normalized.as_bytes()).ok()?;
            (*sym) as *const () as *const u8
        };

        // Cache for future lookups
        self.cache.borrow_mut().insert(normalized.to_string(), ptr);
        Some(ptr)
    }

    fn symbols(&self) -> &[&'static str] {
        RUNTIME_SYMBOL_NAMES
    }

    fn abi_version(&self) -> AbiVersion {
        self.abi_version
    }

    fn name(&self) -> &str {
        self.path.to_str().unwrap_or("dynamic")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn test_default_library_name() {
        let name = DynamicSymbolProvider::default_library_name();
        assert!(!name.is_empty());

        #[cfg(target_os = "linux")]
        assert!(name.ends_with(".so"));

        #[cfg(target_os = "macos")]
        assert!(name.ends_with(".dylib"));

        #[cfg(target_os = "windows")]
        assert!(name.ends_with(".dll"));
    }

    #[test]
    fn test_load_nonexistent_returns_error() {
        let result = DynamicSymbolProvider::load(Path::new("/nonexistent/path/to/lib.so"));
        assert!(result.is_err());
        match result {
            Err(DynLoadError::LibraryNotFound(_)) | Err(DynLoadError::LoadError(_)) => (),
            _ => panic!("Expected LibraryNotFound or LoadError"),
        }
    }

    #[test]
    fn test_runtime_library_candidates_try_variants_before_scalar() {
        let temp = tempfile::tempdir().unwrap();
        let default_path = temp.path().join(DynamicSymbolProvider::default_library_name());
        let candidates = DynamicSymbolProvider::runtime_library_candidates(&default_path, SimdTier::X86_64Avx512);
        let names = candidates
            .iter()
            .map(|value| value.file_name().unwrap().to_string_lossy().to_string())
            .collect::<Vec<_>>();
        assert_eq!(
            names,
            vec![
                DynamicSymbolProvider::variant_library_name(SimdTier::X86_64Avx2),
                DynamicSymbolProvider::variant_library_name(SimdTier::X86_64Sse2),
                DynamicSymbolProvider::default_library_name().to_string(),
            ]
        );
    }

    #[test]
    fn test_load_prefers_best_available_sibling_variant() {
        let temp = tempfile::tempdir().unwrap();
        let avx2 = temp
            .path()
            .join(DynamicSymbolProvider::variant_library_name(SimdTier::X86_64Avx2));
        let scalar = temp.path().join(DynamicSymbolProvider::default_library_name());
        fs::write(&avx2, b"not a library").unwrap();
        fs::write(&scalar, b"not a library either").unwrap();

        let err = match DynamicSymbolProvider::load(&scalar) {
            Ok(_) => panic!("expected variant-aware load failure"),
            Err(err) => err,
        };
        assert!(matches!(err, DynLoadError::LoadError(_)));
    }
}
