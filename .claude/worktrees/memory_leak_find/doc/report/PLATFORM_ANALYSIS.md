# Platform Support Analysis - Commit zz 2b

## Summary

**Commit:** `2b48645a` - "feat: Complete Track A/B/C - Native backend layout optimization and LLVM backend"

**Platform Support Status:**
- ✅ **Linux:** Fully supported (all features work)
- ⚠️ **FreeBSD:** Partial (native backend works, LLVM needs fix)
- ❌ **macOS:** Not supported (needs Mach-O format)
- ❌ **Windows:** Not supported (needs PE/COFF format)

---

## Changes Made in Commit

### 1. Track A: Test Infrastructure (Platform-Independent)
- ✅ Cross-platform: Test database fixes work everywhere
- No platform-specific code

### 2. Track B: Native Backend Layout Optimization (Linux/FreeBSD Only)
**Files Modified:**
- `src/compiler/backend/native/mod.spl` - ELF emission only
- `src/compiler/backend/native/layout_solver.spl` - Platform-independent
- `src/compiler/backend/native/layout_plan_writer.spl` - Platform-independent
- `src/compiler/mir_data.spl` - Platform-independent

**Platform Issues:**
- ❌ Hardcoded ELF format (line 592: `val platform_byte = 1  # Linux`)
- ❌ Only `emit_elf_x86_64`, `emit_elf_aarch64`, `emit_elf_riscv64` functions
- ❌ No `emit_pe_x86_64` for Windows
- ❌ No `emit_macho_x86_64` for macOS
- ❌ No `emit_macho_aarch64` for macOS (Apple Silicon)

### 3. Track C: LLVM Backend (Hardcoded to Linux)
**Files Modified:**
- `src/compiler/backend/llvm_backend.spl` - Platform-independent logic
- `src/compiler/backend/llvm_ir_builder.spl` - Platform-independent IR generation
- `src/compiler/backend/llvm_type_mapper.spl` - Platform-independent types

**Platform Issues:**
- ❌ `src/compiler/backend/llvm_target.spl:30` - Hardcoded `os = "linux"`
  ```simple
  val os = if bare_metal: "none" else: "linux"  # ❌ Should detect OS
  ```
- ❌ Should generate:
  - `x86_64-unknown-linux-gnu` on Linux
  - `x86_64-unknown-freebsd` on FreeBSD
  - `x86_64-apple-darwin` on macOS
  - `x86_64-pc-windows-msvc` on Windows

### 4. Documentation Files (FreeBSD-specific)
**Added Files:**
- `FREEBSD_*.md` - FreeBSD documentation (8 files)
- `doc/guide/freebsd_*.md` - FreeBSD guides (2 files)
- `scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64` - FreeBSD bootstrap
- ✅ These are documentation only, no code impact

---

## Required Fixes for Cross-Platform Support

### Priority 1: Fix LLVM Target Triple (Critical)

**File:** `src/compiler/backend/llvm_target.spl`

**Current Code (Line 28-31):**
```simple
static fn from_target_with_mode(target: CodegenTarget, bare_metal: bool) -> LlvmTargetTriple:
    """Create target triple with OS or bare-metal mode."""
    val os = if bare_metal: "none" else: "linux"  # ❌ HARDCODED
    val env = if bare_metal: nil else: Some("gnu")
```

**Required Fix:**
```simple
use std.platform.get_host_os

static fn from_target_with_mode(target: CodegenTarget, bare_metal: bool) -> LlvmTargetTriple:
    """Create target triple with OS or bare-metal mode."""
    if bare_metal:
        val os = "none"
        val env = nil
        match target:
            # ... same as before
    else:
        # Detect host OS dynamically
        val host_os = get_host_os()
        val (os, vendor, env) = match host_os:
            case "linux":
                ("linux", "unknown", Some("gnu"))
            case "freebsd":
                ("freebsd", "unknown", nil)
            case "macos":
                # Darwin for macOS
                match target:
                    case X86_64: ("darwin", "apple", nil)
                    case AArch64: ("darwin", "apple", nil)
                    case _: ("darwin", "unknown", nil)
            case "windows":
                ("windows", "pc", Some("msvc"))
            case _:
                # Unknown OS, default to Linux
                ("linux", "unknown", Some("gnu"))

        match target:
            case X86_64:
                LlvmTargetTriple(arch: "x86_64", vendor: vendor, os: os, env: env)
            # ... etc
```

**Impact:** CRITICAL - Without this, LLVM backend generates wrong object format on macOS/Windows/FreeBSD

**Effort:** Medium (2-3 hours)

---

### Priority 2: Native Backend Multi-Format Support (High)

**File:** `src/compiler/backend/native/mod.spl`

**Current:** Only ELF format
**Required:** Add PE (Windows) and Mach-O (macOS) writers

**New Files Needed:**
1. `src/compiler/backend/native/pe_writer.spl` - Windows PE/COFF format (~800 LOC)
2. `src/compiler/backend/native/macho_writer.spl` - macOS Mach-O format (~800 LOC)

**Modifications:**
```simple
fn native_compile_x86_64(module: MirModule, mode: BuildMode) -> Result<[i64], text>:
    # ... instruction selection, register allocation, encoding ...

    # Platform-specific emission
    val host_os = get_host_os()
    match host_os:
        case "linux" | "freebsd":
            emit_elf_x86_64(encoded_funcs, allocated, module)
        case "macos":
            emit_macho_x86_64(encoded_funcs, allocated, module)
        case "windows":
            emit_pe_x86_64(encoded_funcs, allocated, module)
        case _:
            Err("Unsupported platform: {host_os}")
```

**Impact:** HIGH - Native backend currently broken on macOS/Windows

**Effort:** Very High (3-4 weeks for both PE and Mach-O writers)

---

### Priority 3: Runtime FFI Declarations (Medium)

**File:** `src/compiler/backend/llvm_backend.spl`

**Current:** Unix-style runtime declarations
**Issue:** Windows uses different calling conventions and runtime functions

**Required Changes:**
- Add platform-specific declarations
- Windows: Use `__stdcall` or `__cdecl` calling convention
- macOS: Handle name mangling differences

**Impact:** MEDIUM - LLVM backend may generate incorrect calls on Windows

**Effort:** Low-Medium (1-2 days)

---

### Priority 4: llc Detection (Low)

**File:** `src/compiler/backend/llvm_backend.spl`

**Current:**
```simple
val result = shell("command -v llc >/dev/null 2>&1")  # Unix only
```

**Required:**
```simple
val llc_check = if is_windows():
    "where llc >nul 2>&1"  # Windows
else:
    "command -v llc >/dev/null 2>&1"  # Unix
val result = shell(llc_check)
```

**Impact:** LOW - Only affects llc availability check

**Effort:** Very Low (30 minutes)

---

## Refactoring Recommendations

### 1. Extract Platform Layer (Recommended)

**New File:** `src/compiler/backend/platform_adapter.spl`

**Purpose:** Centralize all platform-specific logic

```simple
use std.platform.{get_host_os, get_host_arch}

enum ObjectFormat:
    ELF       # Linux, FreeBSD, *BSD
    PE        # Windows
    MachO     # macOS, iOS
    Wasm      # WebAssembly

fn get_object_format() -> ObjectFormat:
    match get_host_os():
        case "linux" | "freebsd" | "openbsd" | "netbsd": ObjectFormat.ELF
        case "macos": ObjectFormat.MachO
        case "windows": ObjectFormat.PE
        case _: ObjectFormat.ELF  # Default

fn get_llvm_triple_suffix() -> (text, text, text?):
    """Returns (os, vendor, env) for LLVM triple."""
    match get_host_os():
        case "linux": ("linux", "unknown", Some("gnu"))
        case "freebsd": ("freebsd", "unknown", nil)
        case "macos": ("darwin", "apple", nil)
        case "windows": ("windows", "pc", Some("msvc"))
        case _: ("linux", "unknown", Some("gnu"))
```

**Benefits:**
- Single source of truth for platform detection
- Easier to add new platforms
- Cleaner separation of concerns

**Effort:** Medium (1 day)

---

### 2. Split Native Backend by Format (Recommended)

**Current Structure:**
```
src/compiler/backend/native/
├── mod.spl              # All emission code
├── layout_solver.spl
└── layout_plan_writer.spl
```

**Recommended Structure:**
```
src/compiler/backend/native/
├── mod.spl              # Dispatch to format-specific emitters
├── layout_solver.spl    # Platform-independent
├── layout_plan_writer.spl  # Platform-independent
├── elf_writer.spl       # ELF format (Linux/FreeBSD)
├── pe_writer.spl        # PE/COFF format (Windows)
└── macho_writer.spl     # Mach-O format (macOS)
```

**Benefits:**
- Clear separation between formats
- Easier to maintain and test
- Can selectively compile per platform

**Effort:** Medium (2-3 days)

---

### 3. Add Platform-Specific Tests (Recommended)

**New Test Files:**
```
test/platform/
├── linux_native_backend_spec.spl
├── freebsd_native_backend_spec.spl
├── macos_llvm_backend_spec.spl     # Only LLVM backend tests
├── windows_llvm_backend_spec.spl   # Only LLVM backend tests
└── cross_platform_spec.spl         # Tests that should pass everywhere
```

**Benefits:**
- Catch platform-specific regressions
- Verify format-specific output
- CI can run platform-specific tests

**Effort:** Medium (2-3 days)

---

## Implementation Priority

### Immediate (This Week)
1. ✅ **Fix LLVM Target Triple** - 2-3 hours
   - Add platform detection to `llvm_target.spl`
   - Test on Linux, verify FreeBSD
   - Enables LLVM backend on all platforms

### Short Term (1-2 Weeks)
2. **Add Platform Adapter Layer** - 1 day
   - Create `platform_adapter.spl`
   - Refactor existing code to use it

3. **Fix llc Detection** - 30 minutes
   - Add Windows-compatible command check

4. **Add Cross-Platform Tests** - 2 days
   - Create platform-specific test suite

### Medium Term (1-2 Months)
5. **Add PE Writer** (Windows Support) - 2-3 weeks
   - Research PE/COFF format
   - Implement `pe_writer.spl`
   - Test with Windows toolchain

6. **Add Mach-O Writer** (macOS Support) - 2-3 weeks
   - Research Mach-O format
   - Implement `macho_writer.spl`
   - Test on macOS x86_64 and ARM64

### Long Term (Optional)
7. **Split Native Backend by Format** - 2-3 days
   - Extract `elf_writer.spl` from `mod.spl`
   - Clean up module structure

---

## Current Platform Matrix

| Platform | Native Backend | LLVM Backend | Status |
|----------|---------------|--------------|---------|
| **Linux x86_64** | ✅ ELF | ⚠️ (hardcoded triple) | Works |
| **Linux AArch64** | ✅ ELF | ⚠️ (hardcoded triple) | Works |
| **Linux RISC-V** | ✅ ELF | ⚠️ (hardcoded triple) | Works |
| **FreeBSD x86_64** | ✅ ELF | ❌ (wrong triple) | Partial |
| **macOS x86_64** | ❌ (needs Mach-O) | ❌ (wrong triple) | Broken |
| **macOS ARM64** | ❌ (needs Mach-O) | ❌ (wrong triple) | Broken |
| **Windows x86_64** | ❌ (needs PE) | ❌ (wrong triple) | Broken |

**After Priority 1 Fix:**
| Platform | Native Backend | LLVM Backend | Status |
|----------|---------------|--------------|---------|
| **Linux x86_64** | ✅ ELF | ✅ | ✅ Full |
| **FreeBSD x86_64** | ✅ ELF | ✅ | ✅ Full |
| **macOS x86_64** | ❌ (needs Mach-O) | ✅ | ⚠️ LLVM only |
| **Windows x86_64** | ❌ (needs PE) | ✅ | ⚠️ LLVM only |

---

## Conclusion

### Modifications in Commit
- **Good:** Layout optimization is platform-independent
- **Good:** LLVM IR generation is platform-independent
- **Problem:** LLVM target triple hardcoded to Linux
- **Problem:** Native backend only supports ELF (Linux/FreeBSD)

### Immediate Action Required
1. **Fix LLVM target triple** (2-3 hours, critical)
   - Makes LLVM backend work on all platforms
   - Relatively easy fix with big impact

### Refactoring Needed?
- **Yes, but not urgent:** Platform adapter layer would be nice
- **Yes, but low priority:** Split native backend by format
- **Optional:** Platform-specific tests can wait

### Recommendation
**Fix Priority 1 (LLVM target triple) immediately**, then continue with other tracks. PE and Mach-O writers are significant undertakings (2-3 weeks each) and can be deferred to later milestones.
