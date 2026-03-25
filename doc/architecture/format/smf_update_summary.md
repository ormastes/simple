# SMF Format Investigation Summary

**Date:** 2026-02-04
**Task:** Check recent SMF format, update docs, compare Rust vs Simple implementations

---

## Investigation Results

### 1. Format Version Discrepancy Identified

**Found:** The specification claimed v1.1, but actual implementation is v0.1

**Evidence:**
```bash
# Test file shows v0.1
$ hexdump -C test/unit/spec/.simple/build/expect_spec.smf | head -2
00000000  53 4d 46 00 00 01 01 00  ...
                    ^^-^^ major=0, minor=1

# Rust code generates v0.1
rust/compiler/src/smf_builder.rs:69-70:
    version_major: 0,
    version_minor: 1,

# Simple code uses v0.1
src/compiler/linker/smf_writer.spl:17-18:
    val SMF_VERSION_MAJOR: i64 = 0
    val SMF_VERSION_MINOR: i64 = 1
```

### 2. Rust vs Simple Feature Comparison

| Feature Category | Rust Implementation | Simple Implementation | Gap |
|------------------|---------------------|----------------------|-----|
| **Header Structure** | Full 128-byte struct with all v1.1 fields | Only 4 constants | Large |
| **Trailer Reading** | ✅ read_trailer() with v1.1/v1.0 fallback | ❌ Not implemented | Critical |
| **Compression** | ✅ Enum + methods (Zstd/Lz4) | ❌ Not implemented | Medium |
| **Stub Support** | ✅ SMF_FLAG_HAS_STUB + methods | ❌ Not implemented | Medium |
| **App Type Hints** | ✅ SmfAppType enum (Cli/Tui/Gui/etc) | ❌ Not implemented | Low |
| **Prefetch Hints** | ✅ Full implementation | ❌ Not implemented | Low |
| **Window Hints** | ✅ GUI window size hints | ❌ Not implemented | Low |

**Summary:** Rust is significantly ahead with v1.1 infrastructure, but both generate v0.1 files in practice.

### 3. Unexpected Finding: SPK Format

**Discovered:** A separate package format (SPK) exists in Rust but is completely undocumented.

**Location:** `rust/loader/src/package/format.rs`

**SPK vs SMF:**
- **SMF**: Single compiled module (object file or executable)
- **SPK**: Distribution package (SMF + resources + manifest + ZIP)
- **SPK Structure:** Trailer-based with "SPK1" magic, contains settlement, resources, manifest

**Status:** Rust-only, no specification, no Simple implementation

---

## File Updates Made

### 1. Created: `doc/format/smf_implementation_status.md`

Comprehensive analysis document containing:
- Executive summary of version discrepancy
- Feature comparison matrix (Rust vs Simple vs Spec)
- Detailed diffs for each feature category
- Specification accuracy issues
- Implementation task list
- Recommendations

**Key sections:**
- Version Discrepancy (spec says 1.1, code generates 0.1)
- Feature Comparison Matrix (20+ features tracked)
- Detailed Differences (7 major categories)
- Specification Accuracy Issues
- Recommendations and tasks

### 2. Updated: `doc/format/smf_specification.md`

**Changes made:**

**Header update:**
```markdown
# Before:
**Version:** 1.1 (with Generic Template Support & Trailer-Based Header)
**Status:** Current

# After:
**Specification Version:** 1.1 (Planned)
**Implementation Version:** 0.1 (Current)
**Status:** v0.1 Active, v1.1 Planned

⚠️ Implementation Note: This spec documents planned v1.1 format.
Current implementations generate v0.1 format.
```

**File Structure section:**
- Added version note distinguishing v0.1 (current) vs v1.1 (planned)
- Renamed "Layout Overview" → "v1.1 Layout (Trailer-Based Design - PLANNED)"
- Added new section: "v0.1 Layout (Current Implementation)"
- Updated "Pure SMF vs Executable SMF" → "Pure SMF vs Executable SMF (v1.1 Only)"

**New v0.1 Layout diagram:**
```
┌──────────────────────────────────────┐ ← File Start (Offset 0)
│     SMF Header (128 bytes)           │  Header at start
├──────────────────────────────────────┤
│        Section Table                 │
│        Section Data                  │
│        Symbol Table                  │
│        String Table                  │
└──────────────────────────────────────┘ ← File End
```

**Added migration notes:**
- v1.1 loaders try EOF-128 first, fall back to offset 0
- v0.1 files remain valid in v1.1
- No need to rewrite existing files

---

## Key Findings Summary

### Architecture Differences

**Rust Implementation:**
- Has complete v1.1 infrastructure (header struct, enums, methods)
- Supports both v1.1 (trailer) and v1.0 (header at start) reading
- Generates v0.1 files in practice (version_major=0, version_minor=1)
- Includes optimization hints: app type, prefetch, window size

**Simple Implementation:**
- Only has basic constants (SMF_MAGIC, VERSION, FLAGS)
- No header struct (just magic number and version constants)
- No trailer reading capability
- No v1.1 features (compression, stubs, hints)

**Both implementations:**
- Generate v0.1 format (header at offset 0)
- Don't use trailer-based design yet
- Don't use compression
- Don't use executable stubs

### Specification Issues

1. **Aspirational not Descriptive:**
   - Spec documents v1.1 (planned features)
   - Code implements v0.1 (basic features)
   - This is OK but needs clear labeling

2. **Missing Status Markers:**
   - No indication which features are implemented vs planned
   - Now fixed with "Implementation Version" and warnings

3. **Undocumented Formats:**
   - SPK format exists but has no specification
   - Should be documented separately

---

## Recommendations for Next Steps

### Immediate (Documentation)
- ✅ **DONE:** Update specification with version status
- ✅ **DONE:** Add v0.1 layout documentation
- ✅ **DONE:** Create implementation status document
- ⏳ **TODO:** Create SPK specification document

### Short-term (Simple Implementation)
1. Port SmfHeader struct from Rust to Simple
2. Add version checking methods
3. Add trailer reading support (v1.1 compatibility)

### Medium-term (Feature Parity)
1. Port CompressionType enum and methods
2. Add stub support (executable SMF)
3. Port app type hints

### Long-term (v1.1 Generation)
1. Switch to generating v1.1 format with trailer
2. Enable compression by default
3. Add executable SMF support
4. Fully implement template sections

---

## Question Answered

**User asked:** "check smf spec, it start with obj or executable"

**Answer:** Test SMF files are **Pure SMF (object files)**, not executables.

**Evidence:**
- File starts with "SMF\0" magic (no shebang)
- No executable stub
- File permissions: rw-rw-r-- (no +x)
- File type: "data"

**According to specification:**
- **Pure SMF** = Just SMF data (+ trailer in v1.1) → Libraries/modules
- **Executable SMF** = Stub + SMF data (+ trailer in v1.1) → Scripts with chmod +x

Current test files are Pure SMF (v0.1 format with header at offset 0).

---

## Files Reference

**Investigation Files:**
- `rust/runtime/src/loader/smf/header.rs` - Full v1.1 header struct (128 bytes)
- `rust/compiler/src/smf_builder.rs` - Generates v0.1 files
- `src/compiler/linker/smf_writer.spl` - Simple constants only
- `rust/loader/src/package/format.rs` - SPK format (undocumented)

**Documentation Files:**
- `doc/format/smf_specification.md` - Updated with v0.1 vs v1.1 distinction
- `doc/format/smf_implementation_status.md` - New detailed analysis
- `doc/format/smf_update_summary.md` - This file

**Test Files:**
- `test/unit/spec/.simple/build/expect_spec.smf` - v0.1 Pure SMF (219 bytes)
- Header: 53 4d 46 00 00 01 ... (SMF\0, version 0.1)
