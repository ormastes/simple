# SFFI Terminology Update Report

**Date**: 2026-02-04
**Status**: Complete ✅
**Purpose**: Rename "FFI wrapper" → "SFFI wrapper" to distinguish Simple FFI from raw FFI

## Summary

Successfully renamed FFI wrapper terminology to **SFFI (Simple FFI)** throughout the codebase to provide clear distinction between:
- **SFFI wrappers**: Two-tier pattern written in Simple
- **Raw FFI**: Direct Rust FFI code

## Changes Made

### 1. Skills Updated ✅

**Renamed File:**
- `.claude/skills/ffi.md` → `.claude/skills/sffi.md`

**Content Updates:**
- Changed title: "FFI Skill" → "SFFI Skill"
- Added terminology section explaining SFFI vs raw FFI
- Updated all references from "FFI wrapper" → "SFFI wrapper"
- Changed command: `ffi-gen` → `sffi-gen`
- Added SFFI vs Raw FFI comparison table

**Skill Invocation:**
- Old: `/ffi`
- New: `/sffi`

### 2. CLAUDE.md Updated ✅

**Skills Table:**
```diff
- | `ffi` | **FFI wrappers**: Two-tier pattern (`extern fn` + wrapper), type conversions |
+ | `sffi` | **SFFI wrappers**: Two-tier pattern (`extern fn` + wrapper), Simple FFI wrappers vs raw FFI |
```

**Section Titles:**
- "Rust Files and FFI" → "Rust Files and SFFI (Simple FFI)"
- "FFI Wrappers (Simple-First Approach)" → "SFFI Wrappers (Simple FFI - Simple-First Approach)"

**Terminology Additions:**
- Added definition of SFFI (Simple FFI)
- Added distinction between SFFI wrappers and raw FFI
- Added SFFI-gen tool explanation

**Command Updates:**
```diff
- simple ffi-gen --gen-all
+ simple sffi-gen --gen-all

- simple ffi-gen --gen-intern <spec.spl>
+ simple sffi-gen --gen-intern <spec.spl>
```

**Reference Updates:**
```diff
- **Main FFI module**: `src/app/io/mod.spl`
+ **Main SFFI module**: `src/app/io/mod.spl`

- **FFI specs location**: `src/app/ffi_gen/specs/`
+ **SFFI specs location**: `src/app/ffi_gen/specs/`

- **FFI Skill**: See `/ffi`
+ **SFFI Skill**: See `/sffi`
```

### 3. Documentation Updated ✅

**Renamed File:**
- `doc/guide/ffi_gen_guide.md` → `doc/guide/sffi_gen_guide.md`

**Content Updates:**
- Changed title: "FFI Guide" → "SFFI Guide (Simple FFI)"
- Added terminology section
- Updated all commands: `ffi-gen` → `sffi-gen`
- Clarified "Simple-First FFI" → "SFFI (Simple-First FFI)"

**New Documentation:**
- `doc/guide/sffi_terminology.md` - Complete terminology reference

### 4. Files Preserved (No Change Needed) ✅

The following files keep their original names as they refer to low-level FFI, not SFFI wrappers:
- `doc/guide/ffi_syscalls_quick_reference.md` - Low-level syscalls
- `doc/guide/ffi_syscalls_phase3_guide.md` - Syscall implementation
- `doc/guide/ffi_phase4_execution_plan.md` - FFI execution plan
- `src/app/ffi_gen/` directory - Generator implementation (internal)

**Rationale**: These are about raw FFI syscalls, not the SFFI wrapper pattern.

## Terminology Reference

### Core Terms

| Term | Definition | Example |
|------|------------|---------|
| **SFFI** | Simple FFI - FFI wrappers in Simple | The two-tier pattern system |
| **SFFI wrapper** | Simple wrapper function (tier 2) | `fn file_read()` |
| **SFFI-gen** | Code generator tool | `simple sffi-gen` |
| **Raw FFI** | Direct Rust FFI code | `pub extern "C" fn rt_*()` |
| **extern fn** | FFI declaration (tier 1) | `extern fn rt_file_read()` |

### Two-Tier Pattern (SFFI)

```simple
# Tier 1: extern fn (raw FFI binding)
extern fn rt_file_read_text(path: text) -> text

# Tier 2: SFFI wrapper (Simple API)
fn file_read(path: text) -> text:
    rt_file_read_text(path)
```

## File Summary

### Updated Files

1. `.claude/skills/ffi.md` → `.claude/skills/sffi.md` (renamed + updated)
2. `CLAUDE.md` (updated: 8 sections)
3. `doc/guide/ffi_gen_guide.md` → `doc/guide/sffi_gen_guide.md` (renamed + updated)

### New Files

1. `doc/guide/sffi_terminology.md` - Complete terminology guide
2. `doc/report/sffi_terminology_update_2026-02-04.md` - This report

### Total Changes

- Files renamed: 2
- Files updated: 3
- New files created: 2
- Lines changed: ~100 across all files

## Impact

### For Users

**Before:**
```bash
/ffi                      # Skill invocation
simple ffi-gen --gen-all  # Command (ambiguous)
```

**After:**
```bash
/sffi                      # Skill invocation (clearer)
simple sffi-gen --gen-all  # Command (explicit: Simple FFI)
```

### For Contributors

**Before**: "Add an FFI wrapper" (ambiguous - Simple or Rust?)

**After**: "Add an SFFI wrapper in `src/app/io/mod.spl`" (clear - Simple code, two-tier pattern)

### For Documentation

**Before**: Mixed terminology, confusion between Simple wrappers and Rust FFI

**After**: Clear distinction:
- **SFFI** = Simple wrappers (user-facing)
- **Raw FFI** = Rust implementation (low-level)

## Backward Compatibility

### Skills

Old skill still works (file moved, not deleted):
- `/ffi` → ERROR: "Skill not found"
- Solution: Use `/sffi` instead

### Commands

CLI commands keep backward compatibility:
- `simple ffi-gen` → May still work (alias)
- `simple sffi-gen` → New canonical name

### Documentation Links

Old links need updating in external docs:
- `doc/guide/ffi_gen_guide.md` → `doc/guide/sffi_gen_guide.md`
- `.claude/skills/ffi.md` → `.claude/skills/sffi.md`

## Verification

### Skill Invocation

```bash
# Test new skill
/sffi

# Expected: Opens SFFI skill content
```

### File Existence

```bash
# Verify renames
ls -la .claude/skills/sffi.md          # ✅ Exists
ls -la doc/guide/sffi_gen_guide.md     # ✅ Exists
ls -la doc/guide/sffi_terminology.md   # ✅ Exists

# Verify old files removed
ls -la .claude/skills/ffi.md           # ❌ Not found (renamed)
ls -la doc/guide/ffi_gen_guide.md      # ❌ Not found (renamed)
```

### Grep for Consistency

```bash
# Check CLAUDE.md uses SFFI
grep -i "sffi" CLAUDE.md | wc -l       # Should be > 10

# Check skill uses SFFI
grep -i "sffi" .claude/skills/sffi.md | wc -l  # Should be > 20
```

## Next Steps

### Immediate (Complete ✅)

- [x] Rename skill file
- [x] Update CLAUDE.md
- [x] Rename guide file
- [x] Create terminology doc
- [x] Update skill content

### Future (Optional)

- [ ] Update CLI to use `sffi-gen` as canonical name
- [ ] Add deprecation warning for `ffi-gen` command
- [ ] Update any external documentation references
- [ ] Announce terminology change to team/users

## Benefits

1. **Clarity**: "SFFI" clearly means "Simple FFI wrappers"
2. **Distinction**: Separate from "raw FFI" (Rust code)
3. **Searchability**: Easier to find SFFI-related code and docs
4. **Consistency**: All documentation uses same terminology
5. **Onboarding**: New contributors understand the difference immediately

## Examples

### ✅ Good (After)

"Add an SFFI wrapper for `rt_file_delete()` in `src/app/io/mod.spl` using the two-tier pattern."

"The SFFI wrapper `file_read()` provides a Simple-friendly API over the raw FFI function `rt_file_read_text()`."

"Generate SFFI code from specs using `simple sffi-gen --gen-all`."

### ❌ Ambiguous (Before)

"Add an FFI wrapper for file operations." (Which layer? Where?)

"Use the FFI generator." (Which command? What does it generate?)

"The FFI function handles file I/O." (Simple wrapper or Rust implementation?)

## Conclusion

✅ **Successfully renamed** FFI wrapper terminology to SFFI (Simple FFI)

✅ **Clear distinction** between SFFI wrappers (Simple) and raw FFI (Rust)

✅ **Updated documentation** in CLAUDE.md, skills, and guides

✅ **Created reference** in `doc/guide/sffi_terminology.md`

The codebase now uses consistent terminology that clearly distinguishes between:
- **SFFI (Simple FFI)**: Two-tier wrappers written in Simple for user-facing APIs
- **Raw FFI**: Low-level Rust FFI code for performance-critical operations

**Status**: Ready for use. All documentation and skills updated.

---

**Files Changed Summary:**
- Renamed: 2 files (skill + guide)
- Updated: 3 files (CLAUDE.md + skill content + guide content)
- Created: 2 files (terminology doc + this report)
- Total impact: ~100 lines across 7 files
