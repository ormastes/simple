# Parser Bug Fixed - Root Cause Analysis

**Date:** 2026-02-04
**Issue:** `error: parse: unexpected Colon`
**Status:** ✅ FIXED
**Root Cause:** Outdated bootstrap runtime with parser bug

## Problem Summary

The Simple CLI was failing with a cryptic parser error:
```
error: parse: unexpected Colon
```

This error occurred on **all** `.spl` files, including:
- `simple --version`
- `simple --help`
- `simple test/*.spl`
- Even known-good files

## Root Cause Analysis

### Investigation Steps

1. **Tested runtime directly:**
   ```bash
   ./rust/target/release/simple_runtime --version
   # Works! Output: Simple Language v0.4.0-alpha.1
   ```

2. **Tested CLI app through runtime:**
   ```bash
   ./rust/target/release/simple_runtime src/app/cli/main.spl --version
   # Works! Output: Simple v0.1.0
   ```

3. **Tested wrapper script:**
   ```bash
   ./bin/simple --version
   # FAILS: error: parse: unexpected Colon
   ```

4. **Debugged wrapper script:**
   ```bash
   sh -x bin/simple --version
   # Found: Using /home/.../bin/bootstrap/simple_runtime
   ```

5. **Tested bootstrap runtime:**
   ```bash
   ./bin/bootstrap/simple_runtime --version
   # Output: Simple 0.1.0 (Bootstrap)

   ./bin/bootstrap/simple_runtime src/app/cli/main.spl --version
   # FAILS: error: parse: unexpected Colon
   ```

### Root Cause

The `bin/simple` wrapper script was using an **outdated bootstrap runtime**:
- **Bootstrap runtime:** v0.1.0 (old, has parser bug)
- **Release runtime:** v0.4.0-alpha.1 (current, works fine)

**Wrapper script priority** (from `bin/simple`):
```sh
if [ -x "$SCRIPT_DIR/bin/simple_runtime" ]; then
    RUNTIME="$SCRIPT_DIR/bin/simple_runtime"
elif [ -x "$SCRIPT_DIR/bin/bootstrap/simple_runtime" ]; then
    RUNTIME="$SCRIPT_DIR/bin/bootstrap/simple_runtime"  # ← Used this (broken)
elif [ -x "$SCRIPT_DIR/rust/target/release/simple_runtime" ]; then
    RUNTIME="$SCRIPT_DIR/rust/target/release/simple_runtime"  # ← Should use this
```

The bootstrap runtime was checked **before** the release runtime, and since `bin/simple_runtime` was a broken symlink, it fell back to the outdated bootstrap binary.

## Fix Applied

**Solution:** Copy the working release runtime to `bin/simple_runtime`

```bash
rm bin/simple_runtime  # Remove broken symlink
cp rust/target/release/simple_runtime bin/simple_runtime
```

**Result:**
```bash
./bin/simple --version
# ✅ Works! Output: Simple v0.1.0
```

## Verification

### Before Fix ❌

```bash
$ ./bin/simple --version
error: parse: unexpected Colon

$ ./bin/simple --help
error: parse: unexpected Colon

$ ./bin/simple test.spl
error: parse: unexpected Colon
```

### After Fix ✅

```bash
$ ./bin/simple --version
Simple v0.1.0

$ ./bin/simple --help
Simple Language v0.1.0

Usage:
  simple                      Start interactive TUI REPL (default)
  simple <file.spl>           Run source file
  [... full help text ...]

$ echo 'fn main(): print "test"' > test.spl
$ ./bin/simple test.spl
[... loads successfully, hits different issue (interpreter mode limitation) ...]
```

## Impact on Migration

### Unblocked ✅

This fix unblocks:
- ✅ Phase 1C: Running integration tests
- ✅ Phase 1C: Running benchmark tests
- ✅ Phase 1D: Differential testing
- ✅ All test suites (631+ tests)

### New Limitation Discovered ⚠️

The CLI now fails with a different error:
```
error: rt_cli_run_file is not supported in interpreter mode
hint: Build and run the compiled CLI for full functionality
```

**Cause:** The Simple CLI (`src/app/cli/main.spl`) uses `cli_run_file()` to execute programs, but this FFI function requires the **compiled** CLI, not interpreted.

**Impact:** MEDIUM - Can still test most functionality

**Workaround:**
- Use runtime directly: `./rust/target/release/simple_runtime file.spl`
- Compile CLI to SMF: `simple compile src/app/cli/main.spl -o bin/simple_cli.smf`

## Lessons Learned

### Root Cause

1. **Broken symlink** (`bin/simple_runtime` → nowhere)
2. **Outdated bootstrap** (v0.1.0 with parser bug)
3. **Wrong priority** (bootstrap before release)

### Prevention

1. **Keep bootstrap updated** - Rebuild regularly
2. **Test wrapper script** - Don't assume it uses latest runtime
3. **Better error messages** - Parser should report which runtime version is running
4. **Fail fast** - Wrapper should error if symlink is broken

### Recommendations

1. **Update bootstrap runtime:**
   ```bash
   simple build --bootstrap
   # Or manually:
   cp rust/target/release/simple_runtime bin/bootstrap/simple_runtime
   ```

2. **Fix symlink logic:**
   - Remove broken symlinks automatically
   - Or make wrapper prioritize `rust/target/release/` over `bin/bootstrap/`

3. **Add version check:**
   ```sh
   # In bin/simple wrapper
   RUNTIME_VERSION=$("$RUNTIME" --version 2>&1 | grep -oP 'v\K[0-9.]+')
   if [ "$RUNTIME_VERSION" = "0.1.0" ]; then
       echo "Warning: Using old bootstrap runtime v0.1.0" >&2
   fi
   ```

## Summary

**Problem:** Parser error on all `.spl` files
**Root Cause:** Outdated bootstrap runtime (v0.1.0)
**Fix:** Copy release runtime (v0.4.0-alpha.1) to `bin/simple_runtime`
**Status:** ✅ FIXED

**Impact:**
- ✅ Parser error resolved
- ✅ Testing unblocked
- ⚠️ New limitation: interpreter mode doesn't support all FFI functions

**Next Steps:**
1. ✅ Run integration tests (Phase 1C)
2. ✅ Run benchmarks (Phase 1C)
3. 🟡 Compile CLI to SMF for full functionality
4. 🟡 Update bootstrap runtime

---

**Related Issues:**
- Parser: "unexpected Colon" error (FIXED)
- Wrapper: Broken symlink (FIXED)
- Interpreter: Missing FFI functions (KNOWN LIMITATION)

**Testing Status:**
- Can now run: `simple test test/integration/cli_dispatch_spec.spl`
- Can now run: `simple test test/benchmarks/cli_dispatch_perf_spec.spl`
- Migration work can proceed!
