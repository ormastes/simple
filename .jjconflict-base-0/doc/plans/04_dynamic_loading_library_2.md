# Dynamic Loading Library Plan - Part 2

Part of [Dynamic Loading Library Plan](04_dynamic_loading_library.md).

            (true, true, false) => PAGE_READWRITE,
            (true, false, true) => PAGE_EXECUTE_READ,
            (true, false, false) => PAGE_READONLY,
            (false, false, true) => PAGE_EXECUTE,
            _ => PAGE_NOACCESS,
        }
    }
}

impl MemoryAllocator for WindowsAllocator {
    fn allocate(&self, size: usize, _alignment: usize) -> std::io::Result<ExecutableMemory> {
        let ptr = unsafe {
            VirtualAlloc(
                std::ptr::null_mut(),
                size,
                MEM_COMMIT | MEM_RESERVE,
                PAGE_READWRITE,  // Start writable
            )
        };

        if ptr.is_null() {
            return Err(std::io::Error::last_os_error());
        }

        Ok(ExecutableMemory {
            ptr: ptr as *mut u8,
            size,
        })
    }

    fn protect(&self, mem: &ExecutableMemory, prot: Protection) -> std::io::Result<()> {
        let flags = Self::protection_to_flags(prot);
        let mut old_flags = 0u32;

        let result = unsafe {
            VirtualProtect(
                mem.ptr as *mut _,
                mem.size,
                flags,
                &mut old_flags,
            )
        };

        if result == 0 {
            return Err(std::io::Error::last_os_error());
        }

        Ok(())
    }

    fn free(&self, mem: ExecutableMemory) -> std::io::Result<()> {
        let result = unsafe {
            VirtualFree(mem.ptr as *mut _, 0, MEM_RELEASE)
        };

        if result == 0 {
            return Err(std::io::Error::last_os_error());
        }

        Ok(())
    }
}

impl Drop for ExecutableMemory {
    fn drop(&mut self) {
        unsafe {
            VirtualFree(self.ptr as *mut _, 0, MEM_RELEASE);
        }
    }
}
```

---

## Module Loader

### Loader Implementation (loader.rs)

```rust
// crates/loader/src/loader.rs

use std::fs::File;
use std::io::{Read, Seek, SeekFrom};
use std::path::Path;

use crate::smf::*;
use crate::memory::*;
use crate::module::LoadedModule;

pub struct ModuleLoader {
    #[cfg(unix)]
    allocator: LinuxAllocator,
    #[cfg(windows)]
    allocator: WindowsAllocator,
}

impl ModuleLoader {
    pub fn new() -> Self {
        Self {
            #[cfg(unix)]
            allocator: LinuxAllocator::new(),
            #[cfg(windows)]
            allocator: WindowsAllocator::new(),
        }
    }

    /// Load an SMF module from file
    pub fn load(&self, path: &Path) -> Result<LoadedModule, LoadError> {
        let mut file = File::open(path)?;

        // Read header
        let header = SmfHeader::read(&mut file)?;
        self.validate_header(&header)?;

        // Read sections
        file.seek(SeekFrom::Start(header.section_table_offset))?;
        let sections = self.read_sections(&mut file, header.section_count)?;

        // Calculate total memory needed
        let (code_size, data_size) = self.calculate_sizes(&sections);

        // Allocate memory
        let code_mem = self.allocator.allocate(code_size, 4096)?;
        let data_mem = if data_size > 0 {
            Some(self.allocator.allocate(data_size, 4096)?)
        } else {
            None
        };

        // Load sections
        let mut code_offset = 0usize;
        let mut data_offset = 0usize;

        for section in &sections {
            match section.section_type {
                SectionType::Code => {
                    file.seek(SeekFrom::Start(section.offset))?;
                    let slice = unsafe {
                        std::slice::from_raw_parts_mut(
                            code_mem.as_mut_ptr().add(code_offset),
                            section.size as usize,
                        )
                    };
                    file.read_exact(slice)?;
                    code_offset += section.virtual_size as usize;
                }

                SectionType::Data | SectionType::RoData => {
                    if let Some(ref data_mem) = data_mem {
                        file.seek(SeekFrom::Start(section.offset))?;
                        let slice = unsafe {
                            std::slice::from_raw_parts_mut(
                                data_mem.as_mut_ptr().add(data_offset),
                                section.size as usize,
                            )
                        };
                        file.read_exact(slice)?;
                        data_offset += section.virtual_size as usize;
                    }
                }

                SectionType::Bss => {
                    // Zero-initialized, already done by allocator
                    if let Some(ref _data_mem) = data_mem {
                        data_offset += section.virtual_size as usize;
                    }
                }

                _ => {}
            }
        }

        // Read symbol table
        let symbols = self.read_symbols(&mut file, &header)?;

        // Read relocations
        let relocs = self.read_relocations(&mut file, &sections)?;

        // Apply relocations
        let code_slice = unsafe {
            std::slice::from_raw_parts_mut(code_mem.as_mut_ptr(), code_size)
        };

        apply_relocations(
            code_slice,
            &relocs,
            &symbols,
            code_mem.as_ptr() as usize,
            &|name| self.resolve_import(name),
        )?;

        // Set memory protection
        self.allocator.protect(&code_mem, Protection::READ_EXECUTE)?;
        if let Some(ref data_mem) = data_mem {
            self.allocator.protect(data_mem, Protection::READ_ONLY)?;
        }

        Ok(LoadedModule {
            path: path.to_path_buf(),
            header,
            code_mem,
            data_mem,
            symbols,
            version: 1,
        })
    }

    fn validate_header(&self, header: &SmfHeader) -> Result<(), LoadError> {
        // Check platform compatibility
        #[cfg(target_os = "linux")]
        if header.platform != Platform::Any as u8 && header.platform != Platform::Linux as u8 {
            return Err(LoadError::IncompatiblePlatform);
        }

        #[cfg(target_os = "windows")]
        if header.platform != Platform::Any as u8 && header.platform != Platform::Windows as u8 {
            return Err(LoadError::IncompatiblePlatform);
        }

        // Check architecture
        #[cfg(target_arch = "x86_64")]
        if header.arch != Arch::X86_64 as u8 {
            return Err(LoadError::IncompatibleArch);
        }

        Ok(())
    }

    fn read_sections(&self, file: &mut File, count: u32) -> Result<Vec<SmfSection>, LoadError> {
        let mut sections = Vec::with_capacity(count as usize);

        for _ in 0..count {
            let mut buf = [0u8; std::mem::size_of::<SmfSection>()];
            file.read_exact(&mut buf)?;
            let section: SmfSection = unsafe {
                std::ptr::read(buf.as_ptr() as *const SmfSection)
            };
            sections.push(section);
        }

        Ok(sections)
    }

    fn calculate_sizes(&self, sections: &[SmfSection]) -> (usize, usize) {
        let mut code_size = 0usize;
        let mut data_size = 0usize;

        for section in sections {
            match section.section_type {
                SectionType::Code => {
                    code_size += section.virtual_size as usize;
                }
                SectionType::Data | SectionType::RoData | SectionType::Bss => {
                    data_size += section.virtual_size as usize;
                }
                _ => {}
            }
        }

        // Align to page size
        let page_size = 4096;
        code_size = (code_size + page_size - 1) & !(page_size - 1);
        data_size = (data_size + page_size - 1) & !(page_size - 1);

        (code_size, data_size)
    }

    fn read_symbols(&self, file: &mut File, header: &SmfHeader) -> Result<SymbolTable, LoadError> {
        file.seek(SeekFrom::Start(header.symbol_table_offset))?;

        // Read symbol entries
        let mut symbols = Vec::with_capacity(header.symbol_count as usize);
        for _ in 0..header.symbol_count {
            let mut buf = [0u8; std::mem::size_of::<SmfSymbol>()];
            file.read_exact(&mut buf)?;
            let sym: SmfSymbol = unsafe {
                std::ptr::read(buf.as_ptr() as *const SmfSymbol)
            };
            symbols.push(sym);
        }

        // Read string table (follows symbols)
        let mut string_table = Vec::new();
        file.read_to_end(&mut string_table)?;

        Ok(SymbolTable::new(symbols, string_table))
    }

    fn read_relocations(&self, file: &mut File, sections: &[SmfSection]) -> Result<Vec<SmfRelocation>, LoadError> {
        let mut relocs = Vec::new();

        for section in sections {
            if section.section_type == SectionType::Reloc {
                file.seek(SeekFrom::Start(section.offset))?;

                let count = section.size as usize / std::mem::size_of::<SmfRelocation>();
                for _ in 0..count {
                    let mut buf = [0u8; std::mem::size_of::<SmfRelocation>()];
                    file.read_exact(&mut buf)?;
                    let reloc: SmfRelocation = unsafe {
                        std::ptr::read(buf.as_ptr() as *const SmfRelocation)
                    };
                    relocs.push(reloc);
                }
            }
        }

        Ok(relocs)
    }

    fn resolve_import(&self, _name: &str) -> Option<usize> {
        // TODO: Implement import resolution from runtime
        None
    }
}

#[derive(Debug)]
pub enum LoadError {
    Io(std::io::Error),
    InvalidFormat(String),
    IncompatiblePlatform,
    IncompatibleArch,
    UndefinedSymbol(String),
    RelocationFailed(String),
}

impl From<std::io::Error> for LoadError {
    fn from(e: std::io::Error) -> Self {
        LoadError::Io(e)
    }
}

impl From<String> for LoadError {
    fn from(e: String) -> Self {
        LoadError::RelocationFailed(e)
    }
}
```

### Loaded Module (module.rs)

```rust
// crates/loader/src/module.rs

use std::path::PathBuf;
use crate::smf::*;
use crate::memory::ExecutableMemory;

/// A loaded Simple module
pub struct LoadedModule {
    pub path: PathBuf,
    pub header: SmfHeader,
    pub code_mem: ExecutableMemory,
    pub data_mem: Option<ExecutableMemory>,
    pub symbols: SymbolTable,
    pub version: u32,
}

impl LoadedModule {
    /// Get function pointer by name
    pub fn get_function<F>(&self, name: &str) -> Option<F> {
        let sym = self.symbols.lookup(name)?;

        if sym.sym_type != SymbolType::Function {
            return None;
        }

        Some(unsafe {
            self.code_mem.get_fn(sym.value as usize)
        })
    }

    /// Get entry point (for executables)
    pub fn entry_point<F>(&self) -> Option<F> {
        if !self.header.is_executable() {
            return None;
        }

        Some(unsafe {
            self.code_mem.get_fn(self.header.entry_point as usize)
        })
    }

    /// Check if module supports hot reload
    pub fn is_reloadable(&self) -> bool {
        self.header.is_reloadable()
    }

    /// Get module source hash (for rebuild detection)
    pub fn source_hash(&self) -> u64 {
        self.header.source_hash
    }

    /// List all exported symbols
    pub fn exports(&self) -> Vec<(&str, SymbolType)> {
        self.symbols
            .exports()
            .map(|s| (self.symbols.symbol_name(s), s.sym_type))
            .collect()
    }
}
```

---

## Module Registry

```rust
// crates/loader/src/registry.rs

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, RwLock};

use crate::loader::ModuleLoader;
use crate::module::LoadedModule;

/// Global module registry for tracking loaded modules
pub struct ModuleRegistry {
    modules: RwLock<HashMap<PathBuf, Arc<LoadedModule>>>,
    loader: ModuleLoader,
}

impl ModuleRegistry {
    pub fn new() -> Self {
        Self {
            modules: RwLock::new(HashMap::new()),
            loader: ModuleLoader::new(),
        }
    }

    /// Load or get cached module
    pub fn load(&self, path: &Path) -> Result<Arc<LoadedModule>, LoadError> {
        let canonical = path.canonicalize()?;

        // Check cache
        {
            let modules = self.modules.read().unwrap();
            if let Some(module) = modules.get(&canonical) {
                return Ok(Arc::clone(module));
            }
        }

        // Load new module
        let module = Arc::new(self.loader.load(&canonical)?);

        // Cache it
        {
            let mut modules = self.modules.write().unwrap();
            modules.insert(canonical, Arc::clone(&module));
        }

        Ok(module)
    }

    /// Unload a module
    pub fn unload(&self, path: &Path) -> bool {
        let canonical = path.canonicalize().ok();

        if let Some(canonical) = canonical {
            let mut modules = self.modules.write().unwrap();
            modules.remove(&canonical).is_some()
        } else {
            false
        }
    }

    /// Reload a module (for hot reload)
    pub fn reload(&self, path: &Path) -> Result<Arc<LoadedModule>, LoadError> {
        let canonical = path.canonicalize()?;

        // Load new version
        let new_module = Arc::new(self.loader.load(&canonical)?);

        // Replace in cache
        {
            let mut modules = self.modules.write().unwrap();
            modules.insert(canonical, Arc::clone(&new_module));
        }

        Ok(new_module)
    }

    /// Resolve symbol across all loaded modules
    pub fn resolve_symbol(&self, name: &str) -> Option<usize> {
        let modules = self.modules.read().unwrap();

        for module in modules.values() {
            if let Some(sym) = module.symbols.lookup(name) {
                if sym.binding == SymbolBinding::Global {
                    let addr = module.code_mem.as_ptr() as usize + sym.value as usize;
                    return Some(addr);
                }
            }
        }

        None
    }
}

use crate::loader::LoadError;
```

---

## Usage Example

```rust
use simple_loader::{ModuleRegistry, LoadError};
use std::path::Path;

fn main() -> Result<(), LoadError> {
    let registry = ModuleRegistry::new();

    // Load a module
    let module = registry.load(Path::new("mylib.smf"))?;

    // Get a function
    type AddFn = extern "C" fn(i64, i64) -> i64;
    let add: AddFn = module.get_function("add").expect("add not found");

    // Call it
    let result = add(2, 3);
    println!("2 + 3 = {}", result);

    // Run executable module
    let exe = registry.load(Path::new("main.sme"))?;
    type MainFn = extern "C" fn() -> i32;
    if let Some(main) = exe.entry_point::<MainFn>() {
        let exit_code = main();
        println!("Exit code: {}", exit_code);
    }

    Ok(())
}
```

---

## Cargo.toml

```toml
[package]
name = "simple-loader"
version = "0.1.0"
edition = "2021"

[dependencies]

[target.'cfg(unix)'.dependencies]
libc = "0.2"

[target.'cfg(windows)'.dependencies]
windows-sys = { version = "0.52", features = [
    "Win32_System_Memory",
] }
```

---

## Summary

| Component | Purpose |
|-----------|---------|
| `smf/` | SMF format parsing |
| `memory/` | Cross-platform executable memory |
| `loader.rs` | Load SMF files into memory |
| `module.rs` | Loaded module handle |
| `registry.rs` | Module caching and symbol resolution |

This provides the foundation for loading compiled Simple modules and enables hot-reloading capability.
---

Back to: [Part 1](04_dynamic_loading_library.md)
