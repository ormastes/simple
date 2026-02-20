# SFFI Terminology Guide

**Date**: 2026-02-04
**Purpose**: Clarify terminology to distinguish Simple FFI wrappers from raw FFI code

## Terminology

### SFFI (Simple FFI)

**SFFI** = **S**imple **FFI** - FFI wrappers written in Simple language using the two-tier pattern.

| Term | Meaning | Example |
|------|---------|---------|
| **SFFI** | Simple FFI wrappers | The entire two-tier pattern system |
| **SFFI wrapper** | Simple wrapper function | `fn file_read()` that calls `extern fn rt_file_read()` |
| **SFFI-gen** | SFFI code generator | `simple sffi-gen --gen-all` |
| **SFFI module** | Module with SFFI wrappers | `src/app/io/mod.spl` |
| **SFFI spec** | Spec for generating FFI | Files in `src/app/ffi_gen/specs/*.spl` |

### Raw FFI

**Raw FFI** = Direct FFI code without the SFFI wrapper pattern.

| Term | Meaning | Example |
|------|---------|---------|
| **Raw FFI** | Direct Rust FFI | `pub extern "C" fn rt_file_read()` in Rust |
| **extern fn** | FFI declaration in Simple | `extern fn rt_file_read(...)` (tier 1 of SFFI) |
| **FFI syscalls** | Low-level system calls | `doc/guide/ffi_syscalls_*.md` |

## Why the Change?

### Problem

The term "FFI wrapper" was ambiguous:
- Did it mean the Simple wrapper function?
- Did it mean the entire two-tier system?
- Was it different from "raw FFI" in Rust?

### Solution

**SFFI** clearly distinguishes:
1. **SFFI wrappers** (Simple) - User-facing, two-tier pattern
2. **Raw FFI** (Rust) - Low-level, performance-critical only

## Two-Tier Pattern (SFFI)

```simple
# Tier 1: extern fn declaration (raw FFI binding)
extern fn rt_file_read_text(path: text) -> text

# Tier 2: SFFI wrapper (Simple-friendly API)
fn file_read(path: text) -> text:
    rt_file_read_text(path)
```

**Together**, these two tiers form an **SFFI wrapper**.

## File Organization

### SFFI Files (Simple)

| Path | Purpose |
|------|---------|
| `src/app/io/mod.spl` | Main SFFI wrapper module |
| `src/lib/io/*.spl` | Stdlib SFFI wrappers |
| `src/app/ffi_gen/specs/*.spl` | SFFI generation specs |

### Raw FFI Files (Rust)

| Path | Purpose |
|------|---------|
| `rust/runtime/src/ffi/*.rs` | Low-level FFI implementations |
| `build/rust/ffi_gen/src/*.rs` | Generated from SFFI specs |

## Commands

| Old Command | New Command | Purpose |
|-------------|-------------|---------|
| `simple ffi-gen --gen-all` | `simple sffi-gen --gen-all` | Generate SFFI code |
| `simple ffi-gen --gen-intern spec.spl` | `simple sffi-gen --gen-intern spec.spl` | Generate single SFFI module |

**Note**: The command name change is for documentation clarity. The actual CLI command may still be `ffi-gen` for backward compatibility.

## Skills and Documentation

| Old Reference | New Reference | Type |
|---------------|---------------|------|
| `/ffi` skill | `/sffi` skill | Skill invocation |
| `doc/guide/ffi_gen_guide.md` | `doc/guide/sffi_gen_guide.md` | Guide |
| `.claude/skills/ffi.md` | `.claude/skills/sffi.md` | Skill file |

## When to Use What

### Use SFFI Wrappers (Simple) When:

✅ Creating user-facing APIs
✅ Adding type conversions
✅ Providing Simple idioms (`.?`, optional chaining, etc.)
✅ Wrapping existing raw FFI

**Example**: All functions in `src/app/io/mod.spl`

### Use Raw FFI (Rust) When:

✅ Performance-critical paths (tight loops)
✅ Direct C library interop
✅ System-level operations
✅ Generated code from SFFI specs

**Example**: `rt_file_read_text()` implementation in Rust runtime

## Migration Guide

### For Users

No action needed. The `/sffi` skill works the same as `/ffi` but with clearer terminology.

### For Contributors

When adding new FFI:
1. Write SFFI wrappers in `src/app/io/mod.spl`
2. Use the two-tier pattern
3. Reference `/sffi` skill for patterns
4. Use `simple sffi-gen` for code generation (if needed)

### For Documentation

When writing docs:
- Use "SFFI wrapper" for the two-tier pattern in Simple
- Use "raw FFI" for direct Rust FFI code
- Use "SFFI-gen" for the code generator
- Use `doc/guide/sffi_gen_guide.md` for generation guide

## Examples

### ✅ Correct Terminology

"Add an SFFI wrapper in `src/app/io/mod.spl` using the two-tier pattern."

"The SFFI wrapper `file_read()` calls the raw FFI function `rt_file_read_text()`."

"Generate SFFI code using `simple sffi-gen --gen-all`."

### ❌ Ambiguous (Old)

"Add an FFI wrapper." (Which tier? Simple or Rust?)

"Use the FFI generator." (What's it called? What does it generate?)

"The FFI function does X." (Which layer? extern fn or wrapper?)

## Quick Reference

| Want to... | Do this... |
|------------|------------|
| Add new API | Write SFFI wrapper in `src/app/io/mod.spl` |
| Learn patterns | Read `/sffi` skill |
| Generate code | Run `simple sffi-gen --gen-all` |
| Find examples | Check `src/app/io/mod.spl` |
| Understand tiers | Read `doc/guide/sffi_gen_guide.md` |

## See Also

- `/sffi` skill - Complete SFFI patterns and examples
- `doc/guide/sffi_gen_guide.md` - SFFI generation guide
- `CLAUDE.md` - Updated with SFFI terminology
- `src/app/io/mod.spl` - Main SFFI wrapper module

---

**Summary**: SFFI = Simple FFI wrappers (two-tier pattern in Simple). Use "SFFI" when referring to Simple wrappers, "raw FFI" when referring to Rust implementations.
