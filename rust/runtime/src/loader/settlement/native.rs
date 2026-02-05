//! Native library support for settlement.
//!
//! Handles loading and managing native libraries (static, shared, system).

use std::collections::HashMap;
use std::ffi::CString;
use std::path::{Path, PathBuf};

use super::super::smf::settlement::{NATIVE_LIB_SHARED, NATIVE_LIB_STATIC, NATIVE_LIB_SYSTEM};

/// Handle to a loaded native library.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NativeHandle(pub u32);

impl NativeHandle {
    pub const INVALID: NativeHandle = NativeHandle(u32::MAX);

    pub fn is_valid(&self) -> bool {
        self.0 != u32::MAX
    }

    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }
}

/// Specification for a native library to be added to settlement.
#[derive(Debug, Clone)]
pub enum NativeLibSpec {
    /// Statically linked library (embedded in settlement)
    Static {
        name: String,
        data: Vec<u8>,
        symbols: Vec<String>,
    },
    /// Shared library (loaded at runtime)
    Shared { name: String, path: PathBuf },
    /// System library (loaded from system paths)
    System { name: String },
}

impl NativeLibSpec {
    pub fn name(&self) -> &str {
        match self {
            NativeLibSpec::Static { name, .. } => name,
            NativeLibSpec::Shared { name, .. } => name,
            NativeLibSpec::System { name } => name,
        }
    }

    pub fn lib_type(&self) -> u8 {
        match self {
            NativeLibSpec::Static { .. } => NATIVE_LIB_STATIC,
            NativeLibSpec::Shared { .. } => NATIVE_LIB_SHARED,
            NativeLibSpec::System { .. } => NATIVE_LIB_SYSTEM,
        }
    }
}

/// A loaded native library instance.
pub struct LoadedNativeLib {
    /// Library name
    pub name: String,
    /// Library type
    pub lib_type: u8,
    /// For static libs: pointer to embedded data
    /// For shared/system libs: handle from dlopen/LoadLibrary
    handle: NativeLibHandle,
    /// Cached symbol lookups
    symbols: HashMap<String, usize>,
}

/// Platform-specific library handle.
#[derive(Debug)]
enum NativeLibHandle {
    /// Embedded static library (pointer to data in memory)
    Static(*const u8, usize),
    /// Dynamically loaded library
    #[cfg(unix)]
    Dynamic(*mut std::ffi::c_void),
    #[cfg(windows)]
    Dynamic(*mut std::ffi::c_void),
    /// Not loaded yet
    #[allow(dead_code)]
    Unloaded,
}

// Safety: The handle is just a pointer that can be safely sent between threads
unsafe impl Send for NativeLibHandle {}
unsafe impl Sync for NativeLibHandle {}

impl LoadedNativeLib {
    /// Create from static library data.
    pub fn from_static(name: String, data: *const u8, size: usize) -> Self {
        Self {
            name,
            lib_type: NATIVE_LIB_STATIC,
            handle: NativeLibHandle::Static(data, size),
            symbols: HashMap::new(),
        }
    }

    /// Load a shared library from path.
    #[cfg(unix)]
    pub fn load_shared(name: String, path: &Path) -> Result<Self, String> {
        let path_str = path.to_str().ok_or("Invalid path")?;
        let c_path = CString::new(path_str).map_err(|e| e.to_string())?;

        let handle = unsafe { libc::dlopen(c_path.as_ptr(), libc::RTLD_NOW | libc::RTLD_LOCAL) };

        if handle.is_null() {
            let error = unsafe {
                let err = libc::dlerror();
                if err.is_null() {
                    "Unknown error".to_string()
                } else {
                    std::ffi::CStr::from_ptr(err).to_string_lossy().into_owned()
                }
            };
            return Err(format!("Failed to load {}: {}", path_str, error));
        }

        Ok(Self {
            name,
            lib_type: NATIVE_LIB_SHARED,
            handle: NativeLibHandle::Dynamic(handle),
            symbols: HashMap::new(),
        })
    }

    #[cfg(windows)]
    pub fn load_shared(name: String, path: &Path) -> Result<Self, String> {
        use std::os::windows::ffi::OsStrExt;

        let wide_path: Vec<u16> = path.as_os_str().encode_wide().chain(Some(0)).collect();

        let handle = unsafe { winapi::um::libloaderapi::LoadLibraryW(wide_path.as_ptr()) };

        if handle.is_null() {
            return Err(format!("Failed to load {:?}", path));
        }

        Ok(Self {
            name,
            lib_type: NATIVE_LIB_SHARED,
            handle: NativeLibHandle::Dynamic(handle as *mut _),
            symbols: HashMap::new(),
        })
    }

    #[cfg(not(any(unix, windows)))]
    pub fn load_shared(name: String, _path: &Path) -> Result<Self, String> {
        Err("Shared library loading not supported on this platform".to_string())
    }

    /// Load a system library by name.
    #[cfg(unix)]
    pub fn load_system(name: String) -> Result<Self, String> {
        // Try common library naming conventions
        let lib_names = [format!("lib{}.so", name), format!("lib{}.dylib", name), name.clone()];

        for lib_name in &lib_names {
            let c_name = match CString::new(lib_name.as_str()) {
                Ok(s) => s,
                Err(_) => continue,
            };

            let handle = unsafe { libc::dlopen(c_name.as_ptr(), libc::RTLD_NOW | libc::RTLD_LOCAL) };

            if !handle.is_null() {
                return Ok(Self {
                    name,
                    lib_type: NATIVE_LIB_SYSTEM,
                    handle: NativeLibHandle::Dynamic(handle),
                    symbols: HashMap::new(),
                });
            }
        }

        Err(format!("System library '{}' not found", name))
    }

    #[cfg(windows)]
    pub fn load_system(name: String) -> Result<Self, String> {
        use std::os::windows::ffi::OsStrExt;

        let dll_name = format!("{}.dll", name);
        let wide_name: Vec<u16> = std::ffi::OsStr::new(&dll_name).encode_wide().chain(Some(0)).collect();

        let handle = unsafe { winapi::um::libloaderapi::LoadLibraryW(wide_name.as_ptr()) };

        if handle.is_null() {
            return Err(format!("System library '{}' not found", name));
        }

        Ok(Self {
            name,
            lib_type: NATIVE_LIB_SYSTEM,
            handle: NativeLibHandle::Dynamic(handle as *mut _),
            symbols: HashMap::new(),
        })
    }

    #[cfg(not(any(unix, windows)))]
    pub fn load_system(name: String) -> Result<Self, String> {
        Err("System library loading not supported on this platform".to_string())
    }

    /// Look up a symbol in the library.
    #[cfg(unix)]
    pub fn get_symbol(&mut self, name: &str) -> Option<usize> {
        self.get_symbol_impl(name, |handle, c_name| unsafe {
            let sym = libc::dlsym(handle, c_name.as_ptr());
            if sym.is_null() {
                None
            } else {
                Some(sym as usize)
            }
        })
    }

    #[cfg(windows)]
    pub fn get_symbol(&mut self, name: &str) -> Option<usize> {
        self.get_symbol_impl(name, |handle, c_name| unsafe {
            let sym = winapi::um::libloaderapi::GetProcAddress(handle as _, c_name.as_ptr() as _);
            if sym.is_null() {
                None
            } else {
                Some(sym as usize)
            }
        })
    }

    /// Platform-agnostic symbol lookup implementation
    fn get_symbol_impl<F>(&mut self, name: &str, lookup: F) -> Option<usize>
    where
        F: FnOnce(*mut std::ffi::c_void, &CString) -> Option<usize>,
    {
        // Check cache first
        if let Some(&addr) = self.symbols.get(name) {
            return Some(addr);
        }

        let addr = match &self.handle {
            NativeLibHandle::Static(_data, _size) => {
                // For static libs, we'd need to parse the object format
                // This is a placeholder - real implementation would parse ELF/Mach-O/COFF
                None
            }
            NativeLibHandle::Dynamic(handle) => {
                let c_name = CString::new(name).ok()?;
                lookup(*handle, &c_name)
            }
            NativeLibHandle::Unloaded => None,
        };

        if let Some(a) = addr {
            self.symbols.insert(name.to_string(), a);
        }

        addr
    }

    #[cfg(not(any(unix, windows)))]
    pub fn get_symbol(&mut self, _name: &str) -> Option<usize> {
        None
    }

    /// Check if this is a static library.
    pub fn is_static(&self) -> bool {
        self.lib_type == NATIVE_LIB_STATIC
    }

    /// Check if this is a shared library.
    pub fn is_shared(&self) -> bool {
        self.lib_type == NATIVE_LIB_SHARED
    }

    /// Check if this is a system library.
    pub fn is_system(&self) -> bool {
        self.lib_type == NATIVE_LIB_SYSTEM
    }
}

impl Drop for LoadedNativeLib {
    fn drop(&mut self) {
        match &self.handle {
            NativeLibHandle::Static(_, _) => {
                // Nothing to do for static libs
            }
            #[cfg(unix)]
            NativeLibHandle::Dynamic(handle) => {
                if !handle.is_null() {
                    unsafe {
                        libc::dlclose(*handle);
                    }
                }
            }
            #[cfg(windows)]
            NativeLibHandle::Dynamic(handle) => {
                if !handle.is_null() {
                    unsafe {
                        winapi::um::libloaderapi::FreeLibrary(*handle as _);
                    }
                }
            }
            NativeLibHandle::Unloaded => {}
            #[cfg(not(any(unix, windows)))]
            _ => {}
        }
    }
}

/// Manager for native libraries in a settlement.
pub struct NativeLibManager {
    libraries: Vec<LoadedNativeLib>,
    by_name: HashMap<String, NativeHandle>,
}

impl NativeLibManager {
    pub fn new() -> Self {
        Self {
            libraries: Vec::new(),
            by_name: HashMap::new(),
        }
    }

    /// Add a static library.
    pub fn add_static(&mut self, name: &str, data: *const u8, size: usize) -> NativeHandle {
        let handle = NativeHandle(self.libraries.len() as u32);
        let lib = LoadedNativeLib::from_static(name.to_string(), data, size);
        self.by_name.insert(name.to_string(), handle);
        self.libraries.push(lib);
        handle
    }

    /// Load and add a shared library.
    pub fn add_shared(&mut self, name: &str, path: &Path) -> Result<NativeHandle, String> {
        let lib = LoadedNativeLib::load_shared(name.to_string(), path)?;
        let handle = NativeHandle(self.libraries.len() as u32);
        self.by_name.insert(name.to_string(), handle);
        self.libraries.push(lib);
        Ok(handle)
    }

    /// Load and add a system library.
    pub fn add_system(&mut self, name: &str) -> Result<NativeHandle, String> {
        let lib = LoadedNativeLib::load_system(name.to_string())?;
        let handle = NativeHandle(self.libraries.len() as u32);
        self.by_name.insert(name.to_string(), handle);
        self.libraries.push(lib);
        Ok(handle)
    }

    /// Get a library by handle.
    pub fn get(&self, handle: NativeHandle) -> Option<&LoadedNativeLib> {
        if handle.is_valid() {
            self.libraries.get(handle.as_usize())
        } else {
            None
        }
    }

    /// Get a mutable library by handle.
    pub fn get_mut(&mut self, handle: NativeHandle) -> Option<&mut LoadedNativeLib> {
        if handle.is_valid() {
            self.libraries.get_mut(handle.as_usize())
        } else {
            None
        }
    }

    /// Get a library by name.
    pub fn get_by_name(&self, name: &str) -> Option<&LoadedNativeLib> {
        self.by_name.get(name).and_then(|h| self.get(*h))
    }

    /// Look up a symbol across all libraries.
    pub fn resolve_symbol(&mut self, name: &str) -> Option<usize> {
        for lib in &mut self.libraries {
            if let Some(addr) = lib.get_symbol(name) {
                return Some(addr);
            }
        }
        None
    }

    /// Look up a symbol in a specific library.
    pub fn resolve_symbol_in(&mut self, handle: NativeHandle, name: &str) -> Option<usize> {
        self.get_mut(handle)?.get_symbol(name)
    }

    /// Get number of libraries.
    pub fn len(&self) -> usize {
        self.libraries.len()
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.libraries.is_empty()
    }

    /// Iterate over libraries.
    pub fn iter(&self) -> impl Iterator<Item = (NativeHandle, &LoadedNativeLib)> {
        self.libraries
            .iter()
            .enumerate()
            .map(|(i, lib)| (NativeHandle(i as u32), lib))
    }
}

impl Default for NativeLibManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_native_handle() {
        let h = NativeHandle(5);
        assert!(h.is_valid());
        assert_eq!(h.as_usize(), 5);
        assert!(!NativeHandle::INVALID.is_valid());
    }

    #[test]
    fn test_native_lib_spec() {
        let spec = NativeLibSpec::Static {
            name: "foo".to_string(),
            data: vec![1, 2, 3],
            symbols: vec!["bar".to_string()],
        };
        assert_eq!(spec.name(), "foo");
        assert_eq!(spec.lib_type(), NATIVE_LIB_STATIC);

        let spec2 = NativeLibSpec::System {
            name: "libc".to_string(),
        };
        assert_eq!(spec2.lib_type(), NATIVE_LIB_SYSTEM);
    }

    #[test]
    fn test_native_lib_manager() {
        let mut manager = NativeLibManager::new();
        assert!(manager.is_empty());

        // Add a static lib (with dummy data)
        let data = [0u8; 100];
        let handle = manager.add_static("test", data.as_ptr(), data.len());
        assert!(handle.is_valid());
        assert_eq!(manager.len(), 1);

        let lib = manager.get(handle).unwrap();
        assert!(lib.is_static());
        assert_eq!(lib.name, "test");
    }
}
