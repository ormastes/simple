# Bootstrap Debugging Summary - 2026-02-14

## Problem Analysis

### Root Cause
The bootstrap process fails at Stage 3 because Stage 2 produces a 219-byte stub instead of a full compiler binary.

**Why it fails:**
1. Stage 2 compiles `src/app/cli/main.spl` using `simple_new1`
2. The CLI application calls `rt_cli_handle_compile()` (Rust FFI function)
3. During compilation, this FFI function is not available in interpreter mode
4. Result: A 219-byte stub SMF/binary that can't actually compile anything
5. Stage 3 tries to use this stub to compile → fails immediately

### Error Message
```
error: rt_cli_handle_compile is not supported in interpreter mode
hint: Build and run the compiled CLI for full functionality
Compiled src/app/cli/main.spl -> build/bootstrap/simple_new2
```

The compilation "succeeds" but produces an unusable output.

## Changes Made

### 1. Fixed `compile_to_smf()` in `src/compiler/driver.spl`
**Before:** Called out to bootstrap binary recursively
**After:** Uses Pure Simple compiler implementation directly

```simple
fn compile_to_smf(path: text, output: text) -> Result<text, text>:
    val options = CompileOptions__default()
    options.input_files = [path]
    options.output_file = output
    options.mode = CompileMode.Aot
    options.output_format = OutputFormat.Smf

    val driver = CompilerDriver__create(options)
    val result = driver.compile()
    # ... handle result ...
```

### 2. Fixed `compile_to_smf()` in `src/compiler_core/driver.spl`
Same fix, but in desugared form for the core compiler.

### 3. Updated `cli_compile()` in `src/app/io/cli_ops.spl`
Added fallback to Pure Simple compiler when FFI is unavailable:

```simple
# Check if we should use Pure Simple compiler
val use_pure_simple = rt_env_get("SIMPLE_USE_PURE_COMPILER") == "1"

if use_pure_simple or not has_native_compiler_ffi():
    return cli_compile_pure_simple(...)

# Otherwise use Rust FFI
rt_cli_handle_compile(compile_args)
```

### 4. Updated Bootstrap Script in `src/app/build/bootstrap.spl`
**Changed Stage 2:** Build native executable instead of SMF
**Changed Stage 3:** Use simple_new2 directly instead of through runtime

```simple
# Stage 2
val compile_cmd = "SIMPLE_COMPILE_RUST=1 {stage1_binary} compile src/app/cli/main.spl --format=native -o {stage2_path}"

# Stage 3
val compile_cmd = "SIMPLE_COMPILE_RUST=1 {stage2_binary} compile src/app/cli/main.spl --format=native -o {stage3_path}"
```

## Remaining Issues

### Issue 1: Bootstrap Script Changes Not Active
The changes to `src/app/build/bootstrap.spl` won't take effect until `bin/simple` is rebuilt.

**Solution:** Rebuild the binary:
```bash
# Option A: Use existing build system
bin/simple build --release

# Option B: Manual bootstrap
cd /home/ormastes/dev/pub/simple
./scripts/bootstrap-minimal.sh
```

### Issue 2: Pure Simple Compiler Not Fully Integrated
The `cli_compile_pure_simple()` function currently returns an error because direct import of `compiler.driver` isn't working.

**Current Implementation:**
```simple
fn cli_compile_pure_simple(...) -> i64:
    _cli_eprint("error: rt_cli_handle_compile is not supported in interpreter mode")
    return 1
```

**Needed:** Actually use the compiler.driver module to compile:
```simple
use compiler.driver.{compile_to_smf}

fn cli_compile_pure_simple(source_file: text, output_file: text, ...) -> i64:
    match compile_to_smf(source_file, output_file):
        case Ok(_):
            return 0
        case Err(msg):
            _cli_eprint(msg)
            return 1
```

### Issue 3: Module Import During Compilation
When compiling `src/app/cli/main.spl`, the compiler needs to resolve all imports including the compiler itself. This creates a circular dependency issue.

**Why it's a problem:**
- `src/app/cli/main.spl` imports `app.io.mod`
- Which imports `app.io.cli_ops`
- Which calls `rt_cli_handle_compile()` (FFI)
- FFI not available during compilation in interpreter mode

**Possible Solutions:**
1. Build the CLI in two stages (stub first, then full)
2. Use conditional compilation to exclude compiler functionality during bootstrap
3. Make the compiler functionality lazy-loaded
4. Build directly to native using seed.cpp → compiler_core → compiler

## Recommended Fix Path

### Option A: Use Seed Compiler Path (Fastest)
1. Use `seed.cpp` to compile `src/compiler_core/` → produces `core_compiler`
2. Use `core_compiler` to compile `src/compiler/` → produces `full_compiler`
3. Use `full_compiler` to compile itself → verify reproducibility

This avoids the circular dependency issue entirely.

### Option B: Fix Pure Simple Integration (More Work)
1. Make `cli_compile()` properly use `compiler.driver.compile_to_smf()`
2. Ensure module imports work correctly during compilation
3. Test with: `SIMPLE_USE_PURE_COMPILER=1 simple_new1 compile ...`
4. Once working, rebuild `bin/simple` with the fixes
5. Run full bootstrap test

### Option C: Change Bootstrap Strategy (Simplest)
Instead of trying to make SMF/Pure Simple work, just build native executables:

1. Stage 1: Copy `bin/release/simple` → `simple_new1`
2. Stage 2: `simple_new1` compiles CLI to **native executable** → `simple_new2`
3. Stage 3: `simple_new2` compiles CLI to native executable → `simple_new3`
4. Verify: `simple_new2 == simple_new3`

This is what I already implemented in the bootstrap script changes, but needs `bin/simple` to be rebuilt.

## Next Steps

### Immediate (To Test Fixes)
1. **Rebuild bin/simple:**
   ```bash
   cd /home/ormastes/dev/pub/simple
   bin/simple build --release
   ```

2. **Test bootstrap:**
   ```bash
   bin/simple build bootstrap
   ```

3. **Check if Stage 2 produces a proper binary:**
   ```bash
   ls -lh build/bootstrap/simple_new2
   file build/bootstrap/simple_new2
   build/bootstrap/simple_new2 --version
   ```

### If That Doesn't Work
1. **Use seed.cpp path:**
   ```bash
   cd seed/build
   cmake .. && make seed_cpp
   cd ../..
   ./scripts/bootstrap-from-scratch.sh
   ```

2. **Or manually test compilation:**
   ```bash
   # Build compiler from compiler_core
   build/bootstrap/simple_new1 compile src/compiler/main.spl -o /tmp/test_compiler
   ```

## Files Modified

1. `src/compiler/driver.spl` - Fixed `compile_to_smf()` to use Pure Simple
2. `src/compiler_core/driver.spl` - Same fix, desugared form
3. `src/app/io/cli_ops.spl` - Added Pure Simple fallback in `cli_compile()`
4. `src/app/build/bootstrap.spl` - Changed to build native executables

## Success Criteria

- [ ] Stage 2 produces a binary > 1MB (not 219 bytes)
- [ ] `simple_new2 --version` works
- [ ] `simple_new2 compile hello.spl` works
- [ ] Stage 3 completes successfully
- [ ] `simple_new2` and `simple_new3` are identical (reproducible build)

## Current Status

**Fixes implemented:** ✅
**Fixes tested:** ❌ (need to rebuild bin/simple)
**Bootstrap working:** ❌

**Blocker:** Need to rebuild `bin/simple` with the updated bootstrap script.

---

**Key Insight:** The Pure Simple compiler already exists and works. We just need to wire it up correctly so that the CLI can use it without depending on Rust FFI.
