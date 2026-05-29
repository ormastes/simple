# SMF Format Implementation Status

**Date:** 2026-02-04
**Status:** Analysis of current Rust vs Simple implementation differences

## Executive Summary

The SMF specification documents v1.1 with trailer-based headers, but **current implementations generate v0.1 format** with headers at offset 0. This document tracks the implementation status across Rust and Simple code.

---

## Version Discrepancy

### Specification Says
- **Version:** 1.1 (documented in `doc/format/smf_specification.md`)
- **Header Location:** EOF-128 (trailer-based, like ZIP format)
- **Features:** Compression, stubs, prefetch hints, app type hints

### Implementation Reality
- **Version Generated:** 0.1 (see actual SMF files and code)
- **Header Location:** Offset 0 (traditional format)
- **Features:** Basic only (no compression, no stubs)

**Test File Evidence:**
```bash
$ hexdump -C test/unit/spec/.simple/build/expect_spec.smf | head -2
00000000  53 4d 46 00 00 01 01 00  01 00 00 00 00 00 00 00  |SMF.............|
          ^^^^^^^^^ ^^^^^ ^^^^^
          SMF\0     v0.1  (major=0, minor=1)
```

---

## Feature Comparison Matrix

| Feature | Rust Impl | Simple Impl | Spec v1.1 | Status |
|---------|-----------|-------------|-----------|---------|
| **Core Format** |
| Basic header (128 bytes) | ✅ Complete | ❌ Constants only | ✅ Yes | Rust ahead |
| Magic validation | ✅ Yes | ❌ Not impl | ✅ Yes | Rust only |
| Version checking | ✅ Yes | ❌ Not impl | ✅ Yes | Rust only |
| **v1.0 Features** |
| Header at offset 0 | ✅ Yes | ✅ Yes | ✅ Yes (compat) | Both |
| Section table | ✅ Yes | ✅ Yes | ✅ Yes | Both |
| Symbol table | ✅ Yes | ✅ Yes | ✅ Yes | Both |
| String table | ✅ Yes | ✅ Yes | ✅ Yes | Both |
| **v1.1 Features** |
| Trailer at EOF-128 | ✅ read_trailer() | ❌ Not impl | ✅ Yes | Rust only |
| Stub support | ✅ Yes | ❌ Not impl | ✅ Yes | Rust only |
| Compression (Zstd/Lz4) | ✅ Enum defined | ❌ Not impl | ✅ Yes | Rust structs only |
| Executable SMF | ✅ SMF_FLAG_HAS_STUB | ❌ Not impl | ✅ Yes | Rust only |
| **Optimization Hints** |
| App type hints | ✅ SmfAppType enum | ❌ Not impl | ✅ Yes | Rust only |
| Prefetch hints | ✅ Yes | ❌ Not impl | ✅ Yes | Rust only |
| Window hints (GUI) | ✅ Yes | ❌ Not impl | ✅ Yes | Rust only |
| **Template Support (v1.1)** |
| TemplateCode section | ⚠️ Partial | ❌ Not impl | ✅ Yes | In progress |
| TemplateMeta section | ⚠️ Partial | ❌ Not impl | ✅ Yes | In progress |
| Template offsets | ⚠️ Partial | ❌ Not impl | ✅ Yes | In progress |

---

## Detailed Differences

### 1. Header Structure

**Rust (`rust/runtime/src/loader/smf/header.rs:9-48`):**
```rust
#[repr(C)]
pub struct SmfHeader {
    // Identification (8 bytes)
    pub magic: [u8; 4],                    // "SMF\0"
    pub version_major: u8,                 // 0 (actually)
    pub version_minor: u8,                 // 1 (actually)
    pub platform: u8,
    pub arch: u8,

    // Flags and counts (20 bytes)
    pub flags: u32,
    pub compression: u8,                   // ⭐ v1.1: Zstd/Lz4
    pub compression_level: u8,             // ⭐ v1.1: 0-22
    pub reserved_compression: [u8; 2],     // ⭐ v1.1: reserved
    pub section_count: u32,
    pub section_table_offset: u64,

    // Symbol table (16 bytes)
    pub symbol_table_offset: u64,
    pub symbol_count: u32,
    pub exported_count: u32,

    // Execution (16 bytes)
    pub entry_point: u64,
    pub stub_size: u32,                    // ⭐ v1.1: executable stub
    pub smf_data_offset: u32,              // ⭐ v1.1: where SMF begins

    // Hashing (16 bytes)
    pub module_hash: u64,
    pub source_hash: u64,

    // Startup optimization hints (12 bytes)
    pub app_type: u8,                      // 0=cli, 1=tui, 2=gui, 3=service, 4=repl
    pub window_width: u16,                 // GUI hint
    pub window_height: u16,                // GUI hint
    pub prefetch_hint: u8,                 // Prefetch files?
    pub prefetch_file_count: u8,           // How many?
    pub reserved: [u8; 5],                 // Padding to 128 bytes

    // Total: 128 bytes
}
```

**Simple (`src/compiler/linker/smf_writer.spl:16-19`):**
```simple
val SMF_MAGIC: i64 = 0x534D4600      # "SMF\0"
val SMF_VERSION_MAJOR: i64 = 0
val SMF_VERSION_MINOR: i64 = 1
val SMF_FLAG_EXECUTABLE: i64 = 0x1
```

**Status:** Simple only has constants, no full header struct.

---

### 2. Trailer Reading (v1.1 Feature)

**Rust (`rust/runtime/src/loader/smf/header.rs:72-111`):**
```rust
/// Read SMF header from trailer (EOF-128) with fallback to v1.0 format.
pub fn read_trailer<R: Read + Seek>(reader: &mut R) -> std::io::Result<Self> {
    let file_size = reader.seek(SeekFrom::End(0))?;

    // Try v1.1 format (trailer at EOF-128)
    if file_size >= Self::SIZE as u64 {
        reader.seek(SeekFrom::Start(file_size - Self::SIZE as u64))?;
        let mut buf = [0u8; Self::SIZE];
        reader.read_exact(&mut buf)?;

        if &buf[0..4] == SMF_MAGIC {
            // Valid v1.1 header at trailer
            return Ok(unsafe { std::ptr::read(buf.as_ptr() as *const SmfHeader) });
        }
    }

    // Fallback to v1.0 format (header at offset 0)
    reader.seek(SeekFrom::Start(0))?;
    // ... read from offset 0 ...
}
```

**Simple:** Not implemented.

**Status:** Rust supports both v1.1 (trailer) and v1.0 (header at start). Simple only v1.0.

---

### 3. Compression Support (v1.1 Feature)

**Rust (`rust/runtime/src/loader/smf/header.rs:420-456`):**
```rust
/// SMF compression type (v1.1+).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum CompressionType {
    None = 0,
    Zstd = 1,  // High ratio
    Lz4 = 2,   // High speed
}

impl SmfHeader {
    pub fn is_compressed(&self) -> bool {
        self.compression != 0
    }

    pub fn get_compression(&self) -> CompressionType {
        CompressionType::from_u8(self.compression)
    }

    pub fn set_compression(&mut self, compression: CompressionType, level: u8) {
        self.compression = compression as u8;
        self.compression_level = level;
    }
}
```

**Simple:** Not implemented.

**Status:** Rust has full enum and methods. Simple has no compression.

---

### 4. Stub Support (Executable SMF, v1.1 Feature)

**Rust (`rust/runtime/src/loader/smf/header.rs:236-243`):**
```rust
pub const SMF_FLAG_HAS_STUB: u32 = 0x0010;

/// Set stub information (v1.1+).
pub fn set_stub_info(&mut self, stub_size: u32, smf_data_offset: u32) {
    self.stub_size = stub_size;
    self.smf_data_offset = smf_data_offset;
    if stub_size > 0 {
        self.flags |= SMF_FLAG_HAS_STUB;
    }
}
```

**Specification (`doc/format/smf_specification.md:52-54`):**
```
┌──────────────────────────────────────┐ ← File Start (Offset 0)
│   [Optional Executable Stub]         │  ⭐ Enables chmod +x ./file.smf
│   #!/usr/bin/env simple              │       and direct execution
│   [ELF/PE/Mach-O stub with SMF]      │
```

**Simple:** Not implemented.

**Status:** Rust ready, Simple missing. Spec documents two types:
- **Pure SMF**: No stub (object/library files)
- **Executable SMF**: Shebang stub + SMF data

---

### 5. Application Type Hints (v1.1 Feature)

**Rust (`rust/runtime/src/loader/smf/header.rs:374-412`):**
```rust
pub enum SmfAppType {
    Cli = 0,      // Command-line tool (minimal resources)
    Tui = 1,      // Terminal UI (terminal mode, buffers)
    Gui = 2,      // Graphical app (window, GPU context)
    Service = 3,  // Background service/daemon
    Repl = 4,     // Interactive REPL
}

impl SmfHeader {
    pub fn get_app_type(&self) -> SmfAppType { ... }
    pub fn set_app_type(&mut self, app_type: SmfAppType) { ... }
    pub fn set_window_hints(&mut self, width: u16, height: u16) { ... }
}
```

**Simple:** Not implemented.

**Purpose:** Allow runtime to optimize resource allocation based on app type.

---

### 6. Prefetch Hints (v1.1 Feature)

**Rust (`rust/runtime/src/loader/smf/header.rs:188-201`):**
```rust
/// Enable prefetching and set expected file count (#1998).
pub fn set_prefetch_hint(&mut self, enabled: bool, file_count: u8) {
    self.prefetch_hint = if enabled { 1 } else { 0 };
    self.prefetch_file_count = file_count;
}

pub fn should_prefetch(&self) -> bool {
    self.prefetch_hint != 0
}

pub fn expected_prefetch_count(&self) -> usize {
    self.prefetch_file_count as usize
}
```

**Simple:** Not implemented.

**Purpose:** Hint to OS for file prefetching to improve startup time.

---

### 7. Package Format (SPK vs SMF)

**Note:** Found a separate **SPK (Simple Package Format)** in `rust/loader/src/package/format.rs`.

**SPK Format:**
```rust
pub const SPK_MAGIC: [u8; 4] = *b"SPK1";

pub struct PackageTrailer {
    pub stub_offset: u64,
    pub stub_size: u64,
    pub settlement_offset: u64,      // SSMF settlement data
    pub settlement_size: u64,
    pub resources_offset: u64,        // ZIP compressed
    pub resources_size: u64,
    pub manifest_offset: u64,         // TOML uncompressed
    pub manifest_size: u64,
    pub settlement_checksum: u32,
    pub resources_checksum: u32,
    pub flags: u16,
    pub version: u16,
    pub magic: [u8; 4],               // "SPK1"
}
```

**Distinction:**
- **SMF**: Single compiled module (object file or executable)
- **SPK**: Distribution package (contains SMF + resources + manifest)

**Status:** SPK is Rust-only, not documented in specification, not in Simple.

---

## Specification Accuracy Issues

### Issue 1: Version Number Mismatch

**Specification claims v1.1:**
```markdown
**Version:** 1.1 (with Generic Template Support & Trailer-Based Header)
**Date:** 2026-01-28
```

**Reality: Code generates v0.1:**
```rust
// rust/compiler/src/smf_builder.rs:69-70
version_major: 0,
version_minor: 1,
```

```simple
// src/compiler/linker/smf_writer.spl:17-18
val SMF_VERSION_MAJOR: i64 = 0
val SMF_VERSION_MINOR: i64 = 1
```

**Test files confirm v0.1:**
```
53 4d 46 00 00 01 ...
            ^^-^^ = major=0, minor=1
```

### Issue 2: Trailer Not Used

**Specification says:**
> An SMF file uses a **ZIP-style trailer** where the header is located at the **end of the file** (EOF-128)

**Reality:**
- Generated SMF files have header at offset 0 (v1.0 style)
- Rust has fallback code: tries trailer, then offset 0
- No files use trailer format in practice

### Issue 3: Features Not Implemented

Specification documents many v1.1 features that aren't generated:
- ❌ Compression (fields exist, but never used)
- ❌ Executable stubs (flag exists, never set)
- ❌ Trailer-based headers (code supports, but never generated)
- ❌ Template sections (partially implemented)

---

## Recommendations

### 1. Update Specification
- Change version from "1.1" to "0.1 (current) / 1.1 (planned)"
- Mark v1.1 features as "planned" not "current"
- Add section: "Implementation Roadmap"

### 2. Port Rust Features to Simple
Priority order:
1. **High Priority:**
   - Full SmfHeader struct with all fields
   - Trailer reading support (v1.1 compatibility)
   - Version checking

2. **Medium Priority:**
   - Compression enum and methods
   - Stub support for executable SMF
   - App type hints

3. **Low Priority:**
   - Prefetch hints
   - Window hints

### 3. Clarify Format Versioning
Create a clear roadmap:
- **v0.1** (current): Basic format, header at offset 0
- **v1.0** (stable): Same as v0.1, but mark as stable
- **v1.1** (future): Trailer-based, compression, stubs, templates

### 4. Document SPK Format
The Simple Package Format (SPK) is implemented but not documented. Should add:
- `doc/format/spk_specification.md`
- Clarify SMF vs SPK distinction
- Document SPK trailer structure

---

## Implementation Tasks

### Task 1: Update Specification (Priority: High)
- [ ] Fix version number: 1.1 → 0.1 (current) / 1.1 (planned)
- [ ] Add "Implementation Status" section
- [ ] Mark v1.1 features as planned
- [ ] Add note about v1.0 fallback

### Task 2: Port Rust Header to Simple (Priority: High)
- [ ] Create full SmfHeader struct in Simple
- [ ] Port all v1.1 fields
- [ ] Add version checking methods
- [ ] Add feature flag methods

### Task 3: Implement Trailer Reading (Priority: Medium)
- [ ] Port read_trailer() to Simple
- [ ] Support v1.1 EOF-128 location
- [ ] Fallback to v1.0 offset 0
- [ ] Add tests for both formats

### Task 4: Add Compression Support (Priority: Low)
- [ ] Port CompressionType enum
- [ ] Add compression methods
- [ ] Integrate with section writing
- [ ] Add zstd/lz4 dependencies

### Task 5: Document SPK Format (Priority: Medium)
- [ ] Create spk_specification.md
- [ ] Document trailer structure
- [ ] Explain SMF vs SPK
- [ ] Add usage examples

---

## Files to Update

1. **Specification:**
   - `doc/format/smf_specification.md` - Fix version, mark features as planned

2. **Simple Implementation:**
   - `src/compiler/linker/smf_writer.spl` - Add full header struct
   - `src/compiler/linker/smf_reader.spl` - Add trailer reading

3. **New Documentation:**
   - `doc/format/spk_specification.md` - Document SPK format
   - `doc/format/smf_roadmap.md` - Version roadmap

---

## Summary

**Current State:**
- Specification claims v1.1, but code generates v0.1
- Rust implementation has v1.1 infrastructure but generates v1.0 files
- Simple implementation only has v1.0 basics
- SPK format exists but undocumented

**Next Steps:**
1. Fix specification version claims
2. Port Rust header structure to Simple
3. Document actual vs planned features clearly
4. Create roadmap for v1.1 features

**Key Finding:**
The specification is **aspirational** (documents v1.1), not **descriptive** (what's actually implemented). This is fine for planning, but needs clear markers about implementation status.
