# Bootstrap Debug Run Findings - 2026-01-29

## Key Discovery

**Stage 1 uses Rust implementation** (`simple_old compile`), not Simple compiler.
- Our debug messages are in `simple/compiler/driver.spl`
- These only appear when Simple-compiled compiler runs
- Therefore: Debug messages will appear in **Stage 2** and later

## Compilation Progress

### Stage 1: simple_old → simple_new1

**Status:** In progress (background task b022143)
**Command:** `RUST_LOG=warn ./target/debug/simple_old compile simple/compiler/main.spl -o target/bootstrap/simple_new1 --native`

**Performance Issue Confirmed:**
- Generated 560,397+ lines of Cranelift IR output
- Log file: 3.6MB after 2 minutes
- Dominated by Cranelift function definitions
- This confirms bug #bootstrap_002 (slow compilation)

**Mitigation Applied:**
- Reduced RUST_LOG to 'warn'
- Filtering out: "defining function", "iconst", "stack_store"
- Should reduce output significantly

### Stage 2: simple_new1 → simple_new2

**Status:** Pending stage 1 completion
**Expected:** This is where we'll see our debug messages!

**Debug Messages to Look For:**
```
[compile] BEFORE phase 3: hir_modules count = N
[compile] AFTER phase 3: new_ctx3.hir_modules count = N
[compile] AFTER assignment: self.ctx.hir_modules count = N

[phase3] parsed modules count=N
[phase3] DEBUG: module_names = [...]
[phase3] stored HIR module 'X', total now: N
[phase3] loop complete. HIR modules keys: [...]
[phase3] returning ctx with N HIR modules

[aot] DEBUG: ctx.hir_modules count = N
[aot] lowering to MIR...
[aot] MIR done, N modules
```

## Bug Analysis

### Bug #bootstrap_001: MIR Gets 0 Modules

**Current Status:** Instrumented, awaiting stage 2 output

**Expected Failure Point:**
- Stage 2 will fail with "No object files to link"
- Debug output will show where N drops to 0

**Possible Scenarios:**

1. **Phase 3 creates 0 modules** (unexpected):
   ```
   [phase3] parsed modules count=0  <-- Bug here
   ```

2. **Phase 3 creates N, but doesn't store** (most likely):
   ```
   [phase3] parsed modules count=1
   [phase3] loop complete. HIR modules keys: []  <-- Bug here
   [phase3] returning ctx with 0 HIR modules  <-- Modules lost in loop
   ```

3. **Context not preserved** (possible):
   ```
   [compile] AFTER phase 3: new_ctx3.hir_modules count = 1
   [compile] AFTER assignment: self.ctx.hir_modules count = 0  <-- Bug here
   ```

4. **Loss between phases** (possible):
   ```
   [compile] AFTER assignment: self.ctx.hir_modules count = 1
   [aot] DEBUG: ctx.hir_modules count = 0  <-- Bug here
   ```

### Bug #bootstrap_002: Slow Compilation

**Status:** Confirmed in stage 1 run

**Evidence:**
- 560,397 lines in 2 minutes
- 3.6MB log file
- Dominated by Cranelift IR dumps

**Impact:**
- Blocks rapid iteration
- Makes debugging difficult
- Causes timeouts

**Proposed Fixes:**
1. **Immediate:** Use `RUST_LOG=warn` by default
2. **Short-term:** Add `--quiet` flag to bootstrap script
3. **Medium-term:** Disable Cranelift IR dumps in non-debug builds
4. **Long-term:** Implement caching to avoid recompilation

## Next Steps

### 1. Wait for Stage 1 Completion
```bash
# Monitor progress
tail -f /tmp/bootstrap_clean.log

# Check if done
ps aux | grep "simple_old compile"
```

### 2. Run Stage 2 with Debug Capture
```bash
# Once stage 1 completes:
./target/bootstrap/simple_new1 -c -o target/bootstrap/simple_new2 simple/compiler/main.spl 2>&1 | tee /tmp/stage2_debug.log
```

### 3. Extract Debug Messages
```bash
grep -E "\[compile\]|\[phase3\]|\[aot\]" /tmp/stage2_debug.log
```

### 4. Analyze Where Modules Are Lost
Compare counts at each phase boundary.

### 5. Apply Fix
Based on findings from step 4.

## Alternative Approach

If stage 1 takes too long, we can:

1. **Test with smaller file:**
   ```bash
   # Use lexer.spl instead of full compiler
   ./target/debug/simple_old compile simple/compiler/lexer.spl -o /tmp/test --native
   ```

2. **Use interpreter mode** (faster):
   ```bash
   # Run compiler in interpret mode
   ./target/debug/simple_old simple/compiler/main.spl
   ```

3. **Skip to stage 2 manually** (if simple_new1 exists from previous run):
   ```bash
   # If we have simple_new1 from earlier
   ./target/bootstrap/simple_new1 -c -o /tmp/test simple/compiler/main.spl
   ```

## Files Created

- `target/bootstrap_debug_20260129_131727.log` - Stage 1 full output (3.6MB)
- `/tmp/bootstrap_clean.log` - Stage 1 filtered output (in progress)
- `/tmp/stage2_debug.log` - Stage 2 output (pending)

## MCP Integration

MCP successfully analyzed code structure but cannot run the actual bootstrap due to:
1. Need for actual compilation (not just analysis)
2. Long compilation times
3. Runtime behavior needed to see bug

**MCP Role:**
- ✅ Code analysis and pattern detection
- ✅ Bug registration and documentation
- ❌ Cannot replace actual runtime debugging
- ❌ Cannot speed up compilation

**Conclusion:** MCP is excellent for static analysis, but runtime bugs require actual execution.
