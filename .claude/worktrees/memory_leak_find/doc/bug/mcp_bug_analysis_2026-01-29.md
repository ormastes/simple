# MCP-Based Bug Analysis - Bootstrap Failure

**Date:** 2026-01-29
**Analyzed By:** MCP-assisted debugging
**Status:** Bugs registered, fixes in progress

---

## Executive Summary

Used MCP server and automated testing to identify and analyze bootstrap compilation bugs. Found **1 critical bug (P0)** blocking self-hosting, **1 performance issue (P1)**, and **closed 1 false positive (P3)**.

---

## Bugs Registered

### Bug #bootstrap_001: MIR Lowering Receives 0 HIR Modules [P0]

**Status:** ✗ Confirmed - Blocking
**Location:** `simple/compiler/driver.spl:699`

**Description:**
Phase 3 (HIR lowering) successfully creates HIR modules, but phase 5 (AOT compilation) finds 0 HIR modules to lower to MIR. This causes linker failure: "No object files to link".

**Evidence:**
```
[phase3] parsed modules count=1
[phase3] processing module: main
[phase3] HIR lowered
[phase3] methods resolved
[compile] phase 3 done

[compile] phase 5: mode-specific processing...
[aot] lowering to MIR...
[aot] MIR done, 0 modules      <-- BUG
Codegen error: Linking failed: No object files to link
```

**Root Cause Analysis:**
- ✓ NOT dictionary mutation semantics (proven by `test_dict_semantics.spl`)
- ✓ NOT class/struct copy issues (both are reference types)
- ? Context flow between phase 3 and phase 5
- ? Possible issue with how `self.ctx` is updated

**Fix Strategy:**
1. **Applied:** Added comprehensive debug logging
   - Phase 3: Log HIR module count after each operation
   - Phase 5: Log HIR module count at start of AOT
   - Context assignment: Log before/after `self.ctx = new_ctx3`

2. **Pending:** Run bootstrap with debug logging to identify exact loss point

3. **Proposed:** Once identified, apply targeted fix

**Reproducible By:**
```bash
./scripts/bootstrap.sh --stage=2
# Fails with "No object files to link"
```

---

### Bug #bootstrap_002: Bootstrap Compilation Extremely Slow [P1]

**Status:** ⚠ Investigating - Performance Issue
**Location:** `simple/compiler/*` (multiple files)

**Description:**
Compiling the compiler (stage 1: simple_old → simple_new1) takes excessive time:
- Expected: <10 seconds
- Actual: >60 seconds (often times out)

This blocks rapid iteration on compiler fixes.

**Contributing Factors:**
- Large debug output (may need `--quiet` flag)
- Possible memory allocation issues
- Tree-sitter parsing overhead
- No caching between compilation phases

**Fix Strategy:**
1. Add performance profiling to identify bottlenecks
2. Implement caching for parsed modules
3. Reduce debug output verbosity
4. Consider incremental compilation

**Reproducible By:**
```bash
time ./target/debug/simple_old compile simple/compiler/main.spl -o /tmp/test
# Takes >60s
```

---

### Bug #dict_semantics_001: Dictionary Mutation Suspected Issue [P3]

**Status:** ✓ Closed - False Positive
**Location:** `simple/compiler/driver.spl:468`

**Description:**
Initially suspected that the pattern `var d = ctx.field; d[key] = value; ctx.field = d` didn't persist mutations.

**Resolution:**
Created test case `scripts/test_dict_semantics.spl` that proves:
- ✓ Copy-modify-reassign pattern works correctly
- ✓ Direct mutation (`ctx.field[key] = value`) works correctly
- ✓ Dictionary semantics are NOT the issue

**Test Results:**
```
=== Test: Copy-Modify-Reassign Pattern ===
Initial count: 0
After mutation count: 1
Value check: 42
✓ PASS: Pattern works correctly

=== Test: Direct Mutation ===
Initial count: 0
After mutation count: 1
✓ PASS: Direct mutation works

=== ALL TESTS PASSED ===
Dictionary semantics are NOT the issue.
```

This bug is **closed** as the suspected issue doesn't exist.

---

## Tools Created

### 1. MCP Debugging Scripts

**`scripts/mcp_debug_bootstrap.spl`**
- Automated bug detection using MCP patterns
- Tests dictionary semantics
- Analyzes driver.spl code patterns
- Generates bug reports automatically

**`scripts/test_dict_semantics.spl`**
- Minimal test case for dictionary mutation
- Tests exact pattern used in driver.spl
- Proves semantics are correct

**`scripts/capture_bootstrap_debug.sh`**
- Captures full debug output from bootstrap
- Extracts relevant phase 3/5 messages
- Saves to timestamped log files

### 2. Debug Instrumentation

**Added to `simple/compiler/driver.spl`:**

```simple
# Phase 3 entry
print "[compile] BEFORE phase 3: hir_modules count = {self.ctx.hir_modules.keys().len()}"

# Phase 3 exit
print "[compile] AFTER phase 3: new_ctx3.hir_modules count = {new_ctx3.hir_modules.keys().len()}"
print "[compile] AFTER assignment: self.ctx.hir_modules count = {self.ctx.hir_modules.keys().len()}"

# Phase 3 loop
print "[phase3] DEBUG: module_names = {module_names}"
print "[phase3] stored HIR module '{name}', total now: {ctx.hir_modules.keys().len()}"
print "[phase3] loop complete. HIR modules keys: {ctx.hir_modules.keys()}"

# Phase 5 AOT entry
print "[aot] DEBUG: ctx.hir_modules count = {self.ctx.hir_modules.keys().len()}"
```

### 3. Bug Database

**`doc/bug/bug_db.sdn`**
- SDN format bug tracking
- Links bugs to test cases
- Tracks investigation notes
- Proposes fix strategies

---

## MCP Analysis Workflow

### 1. Automated Bug Detection
```simple
# Test dictionary semantics
test_dict_mutation() -> Option<Bug>

# Test context mutation
test_context_mutation() -> Option<Bug>

# Analyze code patterns
analyze_driver_code() -> [Bug]
```

### 2. Bug Registration
```simple
# Register bugs to database
register_bugs(bugs: [Bug])

# Generate markdown reports
print_bug(bug: Bug)
```

### 3. Fix Generation
```simple
# Apply automated fixes
apply_fixes(bugs: [Bug])

# Generate patch files
apply_driver_fix()
```

---

## Next Steps

### Immediate (< 1 hour)

1. **Run Bootstrap with Debug Logging**
   ```bash
   ./scripts/capture_bootstrap_debug.sh
   ```
   This will show exactly where HIR modules disappear.

2. **Analyze Debug Output**
   - Check phase 3 "loop complete" message
   - Check phase 5 "ctx.hir_modules count" message
   - Identify the exact point of data loss

3. **Apply Targeted Fix**
   Once we know where modules are lost, apply the fix.

### Short Term (< 1 day)

1. **Complete Bootstrap Pipeline**
   - Fix bug #bootstrap_001
   - Verify generations 2 and 3 are identical
   - Test up to generation 5

2. **Address Performance**
   - Profile compilation bottlenecks
   - Add `--quiet` flag to reduce output
   - Implement basic caching

3. **Enhance MCP Server**
   - Add tools for performance analysis
   - Add tools for context flow tracing
   - Integrate with bug database

### Medium Term (< 1 week)

1. **Automated Testing**
   - Add bootstrap test to CI/CD
   - Run extended bootstrap (5+ generations) nightly
   - Alert on non-deterministic compilation

2. **Self-Hosting Verification**
   - Reach fixpoint where compiler compiles itself identically
   - Benchmark bootstrap performance
   - Document bootstrap process

3. **MCP Integration**
   - Use MCP for live debugging during compilation
   - Automatic bug detection on failed compilations
   - Integration with bug tracking system

---

## Success Metrics

- [ ] Bug #bootstrap_001 fixed - bootstrap reaches generation 2
- [ ] Generations 2 and 3 are bitwise identical (determinism)
- [ ] Bootstrap stage 1 completes in <30 seconds
- [ ] Full 5-generation bootstrap completes without errors
- [ ] MCP server successfully used for debugging

---

## Conclusion

MCP-based analysis successfully:
1. **Identified** critical bootstrap bug
2. **Ruled out** false positive (dictionary semantics)
3. **Added** comprehensive debugging instrumentation
4. **Created** automated testing infrastructure
5. **Registered** bugs in structured database

The bootstrap bug is well-characterized and ready to fix once debug output confirms the exact loss point. All tools are in place for rapid iteration and verification.

**Estimated Time to Fix:** <2 hours once debug output is analyzed

---

## Attachments

- `doc/bug/bug_db.sdn` - Structured bug database
- `doc/bug/bootstrap_mir_zero_modules.md` - Detailed bug report
- `doc/report/bootstrap_investigation_2026-01-29.md` - Investigation report
- `scripts/mcp_debug_bootstrap.spl` - MCP debugger
- `scripts/test_dict_semantics.spl` - Dictionary semantics test
- `scripts/capture_bootstrap_debug.sh` - Debug capture script
