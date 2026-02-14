# Bootstrap Root Cause Analysis - 2026-02-14

## Summary

The bootstrap process cannot work with the current codebase because the Rust source has been removed (100% Pure Simple goal), but the Simple compiler can only produce SMF stubs without the Rust backend.

## Key Discoveries

### 1. No Rust Source Available
- `rust/` directory does not exist
- `bin/release/simple` is a pre-built 27MB ELF binary (last modified Feb 12)
- CLAUDE.md states "100% Pure Simple - No Rust source"
- Cannot rebuild the binary to test source code fixes

### 2. All Compilation Paths Produce 219-Byte SMF Stubs
Tested all compilation methods - all produce identical 219-byte SMF files:
```bash
# All of these produce 219-byte stubs:
bin/release/simple compile hello.spl --format=smf
bin/release/simple compile hello.spl --format=native
bin/release/simple compile hello.spl --format=self-contained
SIMPLE_COMPILE_RUST=1 bin/release/simple compile hello.spl --format=native
```

SMF file structure (hexdump):
- Header: "SMF\0"
- Contains minimal "code" section
- Has "main" entry point
- Valid SMF format, just a stub/bytecode file
- NOT directly executable - requires Simple runtime

### 3. Native Compilation Path Broken
When using `--native` flag (C codegen + gcc):
```
error: codegen: link failed: lld failed:
ld.lld: error: unable to find library -lsimple_compiler
```

The `libsimple_compiler.so` library does not exist anywhere in the project.

### 4. Seed.cpp Bootstrap Path Also Broken
Running `./script/bootstrap-minimal.sh` fails with:
```
build/bootstrap/core1.cpp:7991:33: error: use of undeclared identifier 'BackendKind_Cranelift'
build/bootstrap/core1.cpp:7995:9: error: use of undeclared identifier 'target_is_32bit'
build/bootstrap/core1.cpp:7996:16: error: use of undeclared identifier 'BackendKind_Llvm'
...
```

**Root cause:** Enum mismatch in `src/compiler_core/backend_types.spl` vs usage in `backend_factory.spl`:

**Current enum definition** (`backend_types.spl`):
```simple
enum BackendKind:
    Interpreter
    Compiler
    Sdn
    CraneliftJit
    LlvmJit
    AutoJit
    Custom(name: text)
```

**Usage in code** (`backend_factory.spl`):
```simple
BackendKind.Cranelift   # Should be CraneliftJit?
BackendKind.Llvm        # Should be LlvmJit?
BackendKind.Wasm        # Doesn't exist in enum
BackendKind.Lean        # Doesn't exist in enum
```

Also missing:
- `target_is_32bit()` function
- `target_is_64bit()` function
- `target_is_wasm()` function

### 5. Bootstrap Script Changes Not Active
Modified files:
- `src/compiler/driver.spl` - Uses Pure Simple compiler
- `src/compiler_core/driver.spl` - Fixed (removed Ok/Err)
- `src/app/io/cli_ops.spl` - Fallback to Pure Simple
- `src/app/build/bootstrap.spl` - Build native executables

But changes have no effect because `bin/simple` hasn't been rebuilt with the new code, and can't be rebuilt without Rust source.

## The Circular Dependency Problem

```
User wants: Full Simple compiler buildable by core Simple compiler

Current state:
┌─────────────────────────────────────────────┐
│ seed.cpp (C++)                              │
│   ↓ (transpile & compile)                   │
│ compiler_core (Simple)                      │
│   ✗ BROKEN: enum mismatches                 │
│   ✗ Can't build full compiler               │
└─────────────────────────────────────────────┘

┌─────────────────────────────────────────────┐
│ bin/release/simple (pre-built Rust binary)  │
│   ↓ (interpret Simple source)               │
│ Full compiler (src/compiler/)               │
│   ✗ Only produces 219-byte SMF stubs        │
│   ✗ Can't build itself                      │
└─────────────────────────────────────────────┘
```

## Solutions

### Option A: Fix compiler_core Enum Mismatches (Recommended)
This addresses the original user request: "update full simple buildable by core simple"

**Files to fix:**
1. `src/compiler_core/backend/backend_factory.spl`
   - Update `BackendKind.Cranelift` → `BackendKind.CraneliftJit`
   - Update `BackendKind.Llvm` → `BackendKind.LlvmJit`
   - Remove references to `BackendKind.Wasm`, `BackendKind.Lean`
   - Add stub implementations for `target_is_32bit()`, `target_is_64bit()`, `target_is_wasm()`

2. Search for other files referencing old enum values
3. Test with `./script/bootstrap-minimal.sh`

**Benefits:**
- Directly addresses user's request
- Makes compiler_core self-sufficient
- Enables bootstrap path: seed.cpp → compiler_core → full compiler

### Option B: Restore Rust Source
Not feasible - project goal is 100% Pure Simple.

### Option C: Wait for Pure Simple Compiler Implementation
The `cli_compile_pure_simple()` function exists but isn't implemented:
```simple
fn cli_compile_pure_simple(...) -> i64:
    # Currently returns error
    _cli_eprint("error: rt_cli_handle_compile is not supported in interpreter mode")
    return 1
```

Would need to implement direct import of `compiler.driver.compile_to_smf` and actually use it.

## Recommended Action

Fix the enum mismatches in compiler_core to enable the seed.cpp → compiler_core → full compiler bootstrap path.

**Steps:**
1. Update `backend_factory.spl` enum usage
2. Add missing helper functions
3. Test: `./script/bootstrap-minimal.sh`
4. Use resulting `build/bootstrap/core1` to compile full compiler
5. Verify reproducibility

This is the most direct path to achieving "full simple buildable by core simple."
