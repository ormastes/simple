# SMF v1.1 Summary - Trailer-Based Design

**Date**: 2026-01-28
**Status**: Specification Complete

## Quick Reference

### v1.0 vs v1.1 Comparison

| Feature | v1.0 | v1.1 |
|---------|------|------|
| **Header Location** | Offset 0 (start) | EOF-128 (trailer) ⭐ |
| **Compression** | No built-in support | Yes (default: 0) ⭐ |
| **Executable SMF** | Not supported | Yes (stub support) ⭐ |
| **Generic Templates** | Not stored | Stored (TemplateCode) ⭐ |
| **Direct Execution** | No | Yes (`chmod +x file.smf`) ⭐ |
| **Self-Contained** | No | Yes (native stub) ⭐ |

### File Structure Change

**v1.0 (Header at Start)**:
```
┌──────────────┐ ← Offset 0
│ SMF Header   │ 128 bytes
├──────────────┤
│ Sections...  │
└──────────────┘
```

**v1.1 (Trailer at End)**:
```
┌──────────────┐ ← Offset 0
│ [Stub]       │ Optional (shebang/native)
├──────────────┤
│ Sections...  │
├──────────────┤
│ SMF Header   │ ← EOF-128 (trailer) ⭐
└──────────────┘
```

## New Header Fields (v1.1)

```rust
pub struct SmfHeader {
    // ... existing v1.0 fields ...

    // ⭐ NEW: Compression support
    pub compression: u8,             // 0=none (default), 1=zstd, 2=lz4
    pub compression_level: u8,       // 0=default, 1-22=level
    pub reserved_compression: [u8; 2],

    // ⭐ NEW: Executable SMF support
    pub stub_size: u32,              // Size of prepended stub (0=pure SMF)
    pub smf_data_offset: u32,        // Offset where SMF data begins

    // ⭐ NEW: Template support
    pub template_param_count: u8,    // Number of generic parameters
    pub template_offset: u64,        // Offset to template definition

    // Total: 128 bytes (same size as v1.0)
}
```

## Key Benefits

### 1. Direct Execution (Script Mode)

```bash
#!/usr/bin/env simple
# SMF binary data...

$ chmod +x script.smf
$ ./script.smf  # Runs directly!
```

### 2. Self-Contained Applications

```bash
$ simple compile --self-contained app.spl -o app
$ ./app  # No external runtime needed
```

### 3. Hybrid Binaries

```bash
# Append SMF to native binary
$ gcc main.c -o myapp
$ simple compile plugin.spl -o plugin.smf
$ cat plugin.smf >> myapp
$ ./myapp  # Discovers embedded SMF at runtime
```

### 4. ZIP-Like Design

Similar to ZIP central directory:
- Header at end for streaming-friendly writing
- Optional data at beginning (like self-extracting archives)
- Well-tested pattern in production systems

## Breaking Changes

⚠️ **Header location changed** - v1.0 loaders cannot load v1.1 files.

**Migration**: Update loaders to check EOF-128 first, fallback to offset 0 for v1.0 files.

## Default Compression = 0 (Rationale)

| Reason | Explanation |
|--------|-------------|
| **Direct Execution** | Code sections must be executable without decompression |
| **Shebang Scripts** | Can't decompress before interpreter runs |
| **Fast Startup** | No decompression overhead for most use cases |
| **Selective Compression** | Can enable per-section for data (not code) |

## Implementation Status

✅ **Specification Complete**:
- SMF format specification updated (`doc/format/smf_specification.md`)
- Changelog documented (`doc/format/smf_v1.1_changelog.md`)
- Migration guide provided
- Examples and use cases documented

🚧 **Implementation TODO**:
- Update `src/rust/compiler/src/smf_writer.rs` to write trailer
- Update `src/rust/loader/src/smf/loader.rs` to read from trailer
- Update `simple/compiler/smf_writer.spl` to write trailer
- Add compression support (zstd, lz4)
- Add stub generation for executable SMF
- Add backward compatibility fallback (v1.0 files)

## See Also

- **Full Spec**: `doc/format/smf_specification.md`
- **Changelog**: `doc/format/smf_v1.1_changelog.md`
- **Design Doc**: `doc/design/generic_template_bytecode.md`

---

**Why Trailer Design?**

The trailer-based header (like ZIP format) enables SMF files to be:
1. **Directly executable** (prepend shebang)
2. **Self-contained** (embed in native binaries)
3. **Streaming-friendly** (write sections first, header last)
4. **Flexible** (optional stub at beginning)

This makes SMF files more versatile while maintaining backward compatibility through loader fallback logic.
