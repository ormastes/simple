# Bootstrap Fix Plan - Making Full Simple Compilable by Core Simple

## Problem Summary

**Current State:**
- Stage 1: ✅ Pre-built binary copied successfully
- Stage 2: ✅ Compiles `src/app/cli/main.spl` to `simple_new2.smf` (219 bytes)
- Stage 3: ❌ Fails - `simple_new2.smf` cannot compile (missing functionality)

**Root Cause:**
- `cli_compile()` calls `rt_cli_handle_compile()` (Rust FFI extern function)
- This FFI function is NOT available in interpreter mode or SMF execution
- Result: SMF file is a 219-byte stub that returns immediately
- The compiled SMF has no actual compiler implementation

## Solution

Implement a **Pure Simple compiler** that doesn't rely on Rust FFI.

### Step 1: Create Pure Simple Compiler Entry Point

File: `src/compiler/native_compile.spl`

```simple
# Pure Simple Compiler - No FFI Dependencies
# Can run in interpreter mode or from SMF

use compiler.driver.{compile_file, CompileOptions}
use compiler.backend.{Backend, NativeBackend}
use std.io.{read_file, write_file}

fn compile_simple_to_smf(source_path: text, output_path: text) -> i64:
    # Read source
    val source = read_file(source_path)
    if source == "":
        print "Error: Cannot read source file: {source_path}"
        return 1

    # Parse & compile
    val options = CompileOptions(
        source_file: source_path,
        output_file: output_path,
        target: "x86_64",
        optimize: false,
        debug: true
    )

    val result = compile_file(options)

    match result:
        case Ok(smf_data):
            # Write SMF output
            if write_file(output_path, smf_data):
                print "Compiled {source_path} -> {output_path}"
                return 0
            else:
                print "Error: Cannot write output file: {output_path}"
                return 1
        case Err(error):
            print "Compilation error: {error}"
            return 1
```

### Step 2: Update `cli_compile` to Use Pure Simple Implementation

File: `src/app/io/cli_ops.spl` (line 388)

**Before:**
```simple
fn cli_compile(args: [str]) -> i64:
    # ... parse args ...
    rt_cli_handle_compile(compile_args)  # <-- Rust FFI
```

**After:**
```simple
fn cli_compile(args: [str]) -> i64:
    # ... parse args ...

    # Check if native compiler is available (Rust FFI)
    val use_native = rt_env_get("SIMPLE_COMPILE_RUST") == "1"

    if use_native:
        # Use Rust implementation (faster, for production)
        rt_cli_handle_compile(compile_args)
    else:
        # Use Pure Simple implementation (works in interpreter/SMF mode)
        compile_simple_to_smf(source_file, output_file)
```

### Step 3: Implement Missing Compiler Components

The `src/compiler/` directory has most of the pieces, but they need to be wired together:

**Required Modules:**
- ✅ `lexer.spl` - Tokenization
- ✅ `parser.spl` - AST generation
- ✅ `hir_lowering.spl` - HIR generation
- ✅ `mir_lowering.spl` - MIR generation
- ✅ `backend/` - Code generation
- ❌ `driver.spl` - Pipeline orchestration (NEEDS UPDATE)
- ❌ `smf_writer.spl` - SMF file format writer (NEEDS VERIFICATION)

### Step 4: Test the Bootstrap Chain

```bash
# Stage 1: Use pre-built binary
cp bin/release/simple build/bootstrap/simple_new1

# Stage 2: Compile with simple_new1 (using Pure Simple compiler)
build/bootstrap/simple_new1 compile src/app/cli/main.spl -o build/bootstrap/simple_new2.smf

# Stage 3: Use simple_new2.smf to compile (through runtime)
bin/release/simple build/bootstrap/simple_new2.smf compile src/app/cli/main.spl -o build/bootstrap/simple_new3.smf

# Verify: Stage 2 and Stage 3 should be identical
sha256sum build/bootstrap/simple_new{2,3}.smf
```

## Implementation Priority

### High Priority (Blocking Bootstrap)
1. **Wire up existing compiler modules** in `src/compiler/driver.spl`
2. **Create Pure Simple entry point** for compilation
3. **Update `cli_compile`** to use Pure Simple when FFI unavailable

### Medium Priority (Quality)
4. Verify SMF writer produces valid output
5. Add error handling for compilation failures
6. Test with simple programs first (hello world)

### Low Priority (Optimization)
7. Optimize Pure Simple compiler performance
8. Add caching for repeated compilations
9. Implement incremental compilation

## Success Criteria

- [ ] Stage 2 produces valid SMF file (>1KB, contains actual compiler code)
- [ ] Stage 3 successfully compiles using simple_new2.smf
- [ ] Stage 2 and Stage 3 outputs are identical (reproducible builds)
- [ ] Full compiler can compile itself without Rust FFI dependency

## Timeline Estimate

- **Phase 1 (Wire up compiler)**: 2-4 hours
- **Phase 2 (Update cli_compile)**: 1 hour
- **Phase 3 (Testing & debugging)**: 2-3 hours
- **Total**: 5-8 hours

## Next Steps

1. Read `src/compiler/driver.spl` to understand current pipeline
2. Implement missing glue code to connect modules
3. Test compilation of simple programs
4. Update bootstrap script to use Pure Simple compiler
5. Run full bootstrap test

---

**Key Insight:** The compiler already exists in Pure Simple (`src/compiler/`). We just need to expose it as a callable function instead of only being available through Rust FFI.
