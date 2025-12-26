# Dynamic Loading Library Plan

## Index

| File | Content |
|------|---------|
| [04_dynamic_loading_library.md](04_dynamic_loading_library.md) | Part 1 |
| [04_dynamic_loading_library_2.md](04_dynamic_loading_library_2.md) | Part 2 |

---


## Overview

Implement cross-platform dynamic library loading for Simple language modules (.smf files). This enables hot-reloading and interpreter-like workflow with compiled code.

---

## Architecture

```
┌──────────────────────────────────────────────────────────────┐
│                    Module Loader System                       │
├──────────────────────────────────────────────────────────────┤
│                                                               │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐       │
│  │  .smf File  │───▶│   Loader    │───▶│  Loaded     │       │
│  │  (on disk)  │    │   (parse)   │    │  Module     │       │
│  └─────────────┘    └─────────────┘    └─────────────┘       │
│                            │                   │              │
│                            ▼                   ▼              │
│                     ┌─────────────┐    ┌─────────────┐       │
│                     │  Memory     │    │  Symbol     │       │
│                     │  Allocator  │    │  Table      │       │
│                     │  (exec)     │    │  (lookup)   │       │
│                     └─────────────┘    └─────────────┘       │
│                                                               │
│  Platform Layer                                               │
│  ┌──────────────────┐    ┌──────────────────┐                │
│  │      Linux       │    │     Windows      │                │
│  │  mmap/mprotect   │    │  VirtualAlloc    │                │
│  └──────────────────┘    └──────────────────┘                │
│                                                               │
└──────────────────────────────────────────────────────────────┘
```

---

## File Structure

```
crates/loader/
├── Cargo.toml
└── src/
    ├── lib.rs
    ├── smf/
    │   ├── mod.rs          # SMF format parsing
    │   ├── header.rs       # Header structures
    │   ├── section.rs      # Section handling
    │   ├── symbol.rs       # Symbol table
    │   └── reloc.rs        # Relocation
    ├── memory/
    │   ├── mod.rs          # Memory abstraction
    │   ├── linux.rs        # Linux mmap
    │   └── windows.rs      # Windows VirtualAlloc
    ├── loader.rs           # Main loader logic
    ├── module.rs           # Loaded module handle
    └── registry.rs         # Module registry
```

---

## SMF Format Parsing

### Header (smf/header.rs)

```rust
// crates/loader/src/smf/header.rs

use std::io::{Read, Seek};

pub const SMF_MAGIC: &[u8; 4] = b"SMF\0";

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct SmfHeader {
    pub magic: [u8; 4],
    pub version_major: u8,
    pub version_minor: u8,
    pub platform: u8,
    pub arch: u8,

    pub flags: u32,
    pub section_count: u32,
    pub section_table_offset: u64,

    pub symbol_table_offset: u64,
    pub symbol_count: u32,
    pub exported_count: u32,

    pub entry_point: u64,

    pub module_hash: u64,
    pub source_hash: u64,

    pub reserved: [u8; 8],
}

impl SmfHeader {
    pub const SIZE: usize = 64;

    pub fn read<R: Read>(reader: &mut R) -> std::io::Result<Self> {
        let mut buf = [0u8; Self::SIZE];
        reader.read_exact(&mut buf)?;

        // Validate magic
        if &buf[0..4] != SMF_MAGIC {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "Invalid SMF magic number",
            ));
        }

        Ok(unsafe { std::ptr::read(buf.as_ptr() as *const SmfHeader) })
    }

    pub fn is_executable(&self) -> bool {
        self.flags & SMF_FLAG_EXECUTABLE != 0
    }

    pub fn is_reloadable(&self) -> bool {
        self.flags & SMF_FLAG_RELOADABLE != 0
    }

    pub fn has_debug_info(&self) -> bool {
        self.flags & SMF_FLAG_DEBUG_INFO != 0
    }
}

pub const SMF_FLAG_EXECUTABLE: u32 = 0x0001;
pub const SMF_FLAG_RELOADABLE: u32 = 0x0002;
pub const SMF_FLAG_DEBUG_INFO: u32 = 0x0004;
pub const SMF_FLAG_PIC: u32 = 0x0008;
pub const SMF_FLAG_COMPRESSED: u32 = 0x0010;

#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u8)]
pub enum Platform {
    Any = 0,
    Linux = 1,
    Windows = 2,
    MacOS = 3,
}

#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u8)]
pub enum Arch {
    X86_64 = 0,
    Aarch64 = 1,
}
```

### Section (smf/section.rs)

```rust
// crates/loader/src/smf/section.rs

#[repr(C)]
#[derive(Debug, Clone)]
pub struct SmfSection {
    pub section_type: SectionType,
    pub flags: u32,
    pub offset: u64,
    pub size: u64,
    pub virtual_size: u64,
    pub alignment: u64,
    pub name: [u8; 16],
}

#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u32)]
pub enum SectionType {
    Code = 1,
    Data = 2,
    Bss = 3,
    RoData = 4,
    SymTab = 5,
    Reloc = 6,
    TypeInfo = 7,
    Version = 8,
    SrcMap = 9,
}

impl SmfSection {
    pub fn name_str(&self) -> &str {
        let end = self.name.iter().position(|&b| b == 0).unwrap_or(16);
        std::str::from_utf8(&self.name[..end]).unwrap_or("")
    }

    pub fn is_executable(&self) -> bool {
        self.flags & SECTION_FLAG_EXEC != 0
    }

    pub fn is_writable(&self) -> bool {
        self.flags & SECTION_FLAG_WRITE != 0
    }
}

pub const SECTION_FLAG_READ: u32 = 0x01;
pub const SECTION_FLAG_WRITE: u32 = 0x02;
pub const SECTION_FLAG_EXEC: u32 = 0x04;
```

### Symbol Table (smf/symbol.rs)

```rust
// crates/loader/src/smf/symbol.rs

use std::collections::HashMap;

#[repr(C)]
#[derive(Debug, Clone)]
pub struct SmfSymbol {
    pub name_offset: u32,
    pub name_hash: u32,
    pub sym_type: SymbolType,
    pub binding: SymbolBinding,
    pub visibility: u8,
    pub flags: u8,
    pub value: u64,
    pub size: u64,
    pub type_id: u32,
    pub version: u32,
}

#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u8)]
pub enum SymbolType {
    Function = 1,
    Data = 2,
    Type = 3,
    Trait = 4,
    Actor = 5,
    Constant = 6,
}

#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u8)]
pub enum SymbolBinding {
    Local = 0,
    Global = 1,
    Weak = 2,
}

/// Fast symbol lookup using hash table
pub struct SymbolTable {
    symbols: Vec<SmfSymbol>,
    string_table: Vec<u8>,
    hash_table: HashMap<u32, Vec<usize>>,  // hash -> symbol indices
}

impl SymbolTable {
    pub fn new(symbols: Vec<SmfSymbol>, string_table: Vec<u8>) -> Self {
        let mut hash_table = HashMap::new();

        for (i, sym) in symbols.iter().enumerate() {
            hash_table
                .entry(sym.name_hash)
                .or_insert_with(Vec::new)
                .push(i);
        }

        Self {
            symbols,
            string_table,
            hash_table,
        }
    }

    /// O(1) average lookup by name
    pub fn lookup(&self, name: &str) -> Option<&SmfSymbol> {
        let hash = hash_name(name);

        self.hash_table.get(&hash).and_then(|indices| {
            indices.iter().find_map(|&i| {
                let sym = &self.symbols[i];
                if self.symbol_name(sym) == name {
                    Some(sym)
                } else {
                    None
                }
            })
        })
    }

    pub fn symbol_name(&self, sym: &SmfSymbol) -> &str {
        let start = sym.name_offset as usize;
        let end = self.string_table[start..]
            .iter()
            .position(|&b| b == 0)
            .map(|i| start + i)
            .unwrap_or(self.string_table.len());

        std::str::from_utf8(&self.string_table[start..end]).unwrap_or("")
    }

    /// Get all exported symbols
    pub fn exports(&self) -> impl Iterator<Item = &SmfSymbol> {
        self.symbols
            .iter()
            .filter(|s| s.binding == SymbolBinding::Global)
    }
}

/// FNV-1a hash for symbol names
pub fn hash_name(name: &str) -> u32 {
    const FNV_OFFSET: u32 = 2166136261;
    const FNV_PRIME: u32 = 16777619;

    let mut hash = FNV_OFFSET;
    for byte in name.bytes() {
        hash ^= byte as u32;
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}
```

### Relocation (smf/reloc.rs)

```rust
// crates/loader/src/smf/reloc.rs

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct SmfRelocation {
    pub offset: u64,
    pub symbol_index: u32,
    pub reloc_type: RelocationType,
    pub addend: i64,
}

#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u32)]
pub enum RelocationType {
    None = 0,
    Abs64 = 1,       // Absolute 64-bit address
    Pc32 = 2,        // PC-relative 32-bit
    Plt32 = 3,       // PLT entry call
    GotPcRel = 4,    // GOT entry, PC-relative
}

/// Apply relocations to loaded code
pub fn apply_relocations(
    code: &mut [u8],
    relocs: &[SmfRelocation],
    symbols: &SymbolTable,
    base_address: usize,
    imports: &dyn Fn(&str) -> Option<usize>,
) -> Result<(), String> {
    for reloc in relocs {
        let sym = &symbols.symbols[reloc.symbol_index as usize];
        let sym_name = symbols.symbol_name(sym);

        // Resolve symbol address
        let sym_addr = if sym.binding == SymbolBinding::Local {
            base_address + sym.value as usize
        } else {
            imports(sym_name).ok_or_else(|| {
                format!("Undefined symbol: {}", sym_name)
            })?
        };

        let patch_addr = base_address + reloc.offset as usize;
        let patch_ptr = code.as_mut_ptr().wrapping_add(reloc.offset as usize);

        match reloc.reloc_type {
            RelocationType::Abs64 => {
                let value = sym_addr.wrapping_add(reloc.addend as usize);
                unsafe {
                    *(patch_ptr as *mut u64) = value as u64;
                }
            }

            RelocationType::Pc32 => {
                let value = (sym_addr as i64)
                    .wrapping_sub(patch_addr as i64)
                    .wrapping_add(reloc.addend) as i32;
                unsafe {
                    *(patch_ptr as *mut i32) = value;
                }
            }

            RelocationType::Plt32 => {
                // For now, same as PC32 (direct call)
                let value = (sym_addr as i64)
                    .wrapping_sub(patch_addr as i64)
                    .wrapping_add(reloc.addend) as i32;
                unsafe {
                    *(patch_ptr as *mut i32) = value;
                }
            }

            RelocationType::None | RelocationType::GotPcRel => {}
        }
    }

    Ok(())
}
```

---

## Memory Allocation

### Abstraction (memory/mod.rs)

```rust
// crates/loader/src/memory/mod.rs

#[cfg(unix)]
mod linux;
#[cfg(windows)]
mod windows;

#[cfg(unix)]
pub use linux::*;
#[cfg(windows)]
pub use windows::*;

/// Memory protection flags
#[derive(Debug, Clone, Copy)]
pub struct Protection {
    pub read: bool,
    pub write: bool,
    pub execute: bool,
}

impl Protection {
    pub const READ_ONLY: Self = Self { read: true, write: false, execute: false };
    pub const READ_WRITE: Self = Self { read: true, write: true, execute: false };
    pub const READ_EXECUTE: Self = Self { read: true, write: false, execute: true };
    pub const READ_WRITE_EXECUTE: Self = Self { read: true, write: true, execute: true };
}

/// Executable memory region
pub struct ExecutableMemory {
    ptr: *mut u8,
    size: usize,
}

impl ExecutableMemory {
    pub fn as_ptr(&self) -> *const u8 {
        self.ptr
    }

    pub fn as_mut_ptr(&self) -> *mut u8 {
        self.ptr
    }

    pub fn size(&self) -> usize {
        self.size
    }

    /// Get function pointer at offset
    pub unsafe fn get_fn<F>(&self, offset: usize) -> F {
        std::mem::transmute_copy(&(self.ptr.add(offset) as usize))
    }
}

/// Memory allocator trait
pub trait MemoryAllocator {
    /// Allocate memory with given size and alignment
    fn allocate(&self, size: usize, alignment: usize) -> std::io::Result<ExecutableMemory>;

    /// Set protection on memory region
    fn protect(&self, mem: &ExecutableMemory, prot: Protection) -> std::io::Result<()>;

    /// Free memory
    fn free(&self, mem: ExecutableMemory) -> std::io::Result<()>;
}
```

### Linux Implementation (memory/linux.rs)

```rust
// crates/loader/src/memory/linux.rs

use super::*;
use libc::{mmap, mprotect, munmap, MAP_ANON, MAP_PRIVATE, PROT_EXEC, PROT_NONE, PROT_READ, PROT_WRITE};
use std::ptr;

pub struct LinuxAllocator;

impl LinuxAllocator {
    pub fn new() -> Self {
        Self
    }

    fn protection_to_flags(prot: Protection) -> i32 {
        let mut flags = 0;
        if prot.read { flags |= PROT_READ; }
        if prot.write { flags |= PROT_WRITE; }
        if prot.execute { flags |= PROT_EXEC; }
        if flags == 0 { flags = PROT_NONE; }
        flags
    }
}

impl MemoryAllocator for LinuxAllocator {
    fn allocate(&self, size: usize, alignment: usize) -> std::io::Result<ExecutableMemory> {
        // Round up to page size
        let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize };
        let aligned_size = (size + page_size - 1) & !(page_size - 1);

        let ptr = unsafe {
            mmap(
                ptr::null_mut(),
                aligned_size,
                PROT_READ | PROT_WRITE,  // Start writable for loading
                MAP_PRIVATE | MAP_ANON,
                -1,
                0,
            )
        };

        if ptr == libc::MAP_FAILED {
            return Err(std::io::Error::last_os_error());
        }

        Ok(ExecutableMemory {
            ptr: ptr as *mut u8,
            size: aligned_size,
        })
    }

    fn protect(&self, mem: &ExecutableMemory, prot: Protection) -> std::io::Result<()> {
        let flags = Self::protection_to_flags(prot);

        let result = unsafe {
            mprotect(mem.ptr as *mut _, mem.size, flags)
        };

        if result != 0 {
            return Err(std::io::Error::last_os_error());
        }

        Ok(())
    }

    fn free(&self, mem: ExecutableMemory) -> std::io::Result<()> {
        let result = unsafe {
            munmap(mem.ptr as *mut _, mem.size)
        };

        if result != 0 {
            return Err(std::io::Error::last_os_error());
        }

        Ok(())
    }
}

impl Drop for ExecutableMemory {
    fn drop(&mut self) {
        unsafe {
            munmap(self.ptr as *mut _, self.size);
        }
    }
}
```

### Windows Implementation (memory/windows.rs)

```rust
// crates/loader/src/memory/windows.rs

use super::*;
use windows_sys::Win32::System::Memory::*;

pub struct WindowsAllocator;

impl WindowsAllocator {
    pub fn new() -> Self {
        Self
    }

    fn protection_to_flags(prot: Protection) -> u32 {
        match (prot.read, prot.write, prot.execute) {
            (true, true, true) => PAGE_EXECUTE_READWRITE,
---

Next: [Part 2](04_dynamic_loading_library_2.md)
