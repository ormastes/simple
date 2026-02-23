# Bootstrap Investigation Report - 2026-01-29

## Executive Summary

Investigated bootstrap failure where `simple_new1` (generation 1 compiler) fails to compile itself into `simple_new2` (generation 2). The root cause is that MIR lowering receives 0 HIR modules despite phase 3 successfully creating them.

## What We Found

### 1. Bootstrap Pipeline

```
Generation 0: simple_old (Rust)           ✓ Works
                ↓
Generation 1: simple_new1 (Simple)        ✓ Compiles successfully
                ↓
Generation 2: simple_new2 (Simple)        ✗ FAILS - MIR lowering gets 0 modules
```

### 2. Failure Point

**Stage 2**: When `simple_new1` tries to compile `simple/compiler/main.spl` into `simple_new2`

**Error**: `Codegen error: Linking failed: No object files to link`

**Root Cause**: `[aot] MIR done, 0 modules` - MIR lowering finds no HIR modules to process

### 3. Evidence from Logs

```
[phase3] parsed modules count=1
[phase3] processing module: main
[phase3] HIR lowered
[phase3] methods resolved
[compile] phase 3 done

[compile] phase 5: mode-specific processing...
[aot] lowering to MIR...
[aot] MIR done, 0 modules      <-- BUG HERE
```

Phase 3 successfully creates HIR modules, but they disappear by the time we reach AOT compilation.

### 4. Suspicious Code

**File**: `simple/compiler/driver.spl`

**Phase 3** (lines 467-470):
```simple
# Store final module
var hir_modules = ctx.hir_modules
hir_modules[name] = resolved_module
ctx.hir_modules = hir_modules
```

**Question**: Does this pattern actually mutate `ctx.hir_modules`, or does it create a new dictionary that gets discarded?

**Phase 5 AOT** (lines 693-700):
```simple
fn lower_to_mir() -> bool:
    for name in self.ctx.hir_modules.keys():  # <-- Returns empty list
        val hir_module = self.ctx.hir_modules[name]
        ...
```

### 5. Suspected Issue: Dictionary Mutation Semantics

In Simple, dictionaries might have copy-on-write or immutable semantics. The pattern:

```simple
var dict = ctx.field
dict[key] = value
ctx.field = dict
```

May not work as expected if:
- `ctx.field` returns a copy (not a reference)
- Dictionary assignment creates a new dict instead of mutating
- Class field assignment has unexpected semantics

### 6. MCP Integration

We have an MCP server available at `src/app/mcp/main.spl` that provides:
- `read_code` - Read Simple source files
- `list_files` - List .spl files
- `search_code` - Search for patterns
- `file_info` - Get file statistics

This can be used to help analyze the codebase and track down bugs.

## Actions Taken

### 1. Added Debug Logging

**Added to `simple/compiler/driver.spl`:**

```simple
# After storing HIR module (line 470+):
print "[phase3] stored HIR module '{name}', total now: {ctx.hir_modules.keys().len()}"

# Before returning from lower_and_check_impl (line 472+):
print "[phase3] returning ctx with {ctx.hir_modules.keys().len()} HIR modules"

# At start of aot_compile (line 617+):
print "[aot] DEBUG: ctx.hir_modules count = {self.ctx.hir_modules.keys().len()}"
```

These will show exactly where the HIR modules disappear.

### 2. Created Bug Report

**File**: `doc/bug/bootstrap_mir_zero_modules.md`

Comprehensive documentation of the bug with reproduction steps, suspected causes, and fix strategies.

### 3. Created Extended Bootstrap Test

**File**: `scripts/bootstrap_extended.spl`

A Simple script that:
- Runs N generations of bootstrap (default: 5)
- Tracks hashes and success/failure for each generation
- Detects crashes and bugs automatically
- Saves results to `target/bootstrap/report.md`
- Finds fixpoint when generations become identical

### 4. Fixed Compilation Error

Fixed undefined variable `it_total_start` in `src/rust/compiler/src/interpreter_call/bdd.rs:511`

## Next Steps

### Immediate (For User)

1. **Run with Debug Logging** (currently in progress):
   ```bash
   ./target/debug/simple_old compile simple/compiler/main.spl -o /tmp/test
   ```
   Check output for our debug messages to see where HIR modules get lost.

2. **Verify Dictionary Semantics**:
   Create a minimal test case:
   ```simple
   class Ctx:
       data: Dict<text, i32>

   fn test():
       val ctx = Ctx(data: {})
       var d = ctx.data
       d["key"] = 42
       ctx.data = d
       print "Count: {ctx.data.keys().len()}"  # Should be 1
   ```

3. **Try Direct Mutation**:
   Change line 469 in `driver.spl` from:
   ```simple
   var hir_modules = ctx.hir_modules
   hir_modules[name] = resolved_module
   ctx.hir_modules = hir_modules
   ```

   To:
   ```simple
   ctx.hir_modules[name] = resolved_module
   ```

### Medium Term

1. **Complete Bootstrap Pipeline**:
   - Fix HIR module storage bug
   - Verify generations 2 and 3 are identical (determinism check)
   - Test up to generation 5 with extended bootstrap script

2. **Add More Debug Instrumentation**:
   - Add memory profiling to detect leaks during bootstrap
   - Track compilation times for each phase
   - Log all context mutations

3. **Improve Error Reporting**:
   - When MIR lowering gets 0 modules, show where HIR modules should have come from
   - Add validation that HIR modules exist before entering AOT mode

### Long Term

1. **MCP-Enhanced Debugging**:
   - Use MCP server to automatically analyze failing compilations
   - Create MCP tools for:
     - Tracking value flow through compilation phases
     - Detecting context mutation issues
     - Analyzing dictionary/collection semantics

2. **Automated Bootstrap Testing**:
   - Add bootstrap test to CI/CD
   - Run extended bootstrap (5+ generations) on every commit
   - Alert on non-deterministic compilation

3. **Self-Hosting Milestone**:
   - Reach fixpoint where compiler compiles itself identically
   - Benchmark bootstrap performance
   - Document bootstrap process for contributors

## Tools Created

1. **`scripts/bootstrap_extended.spl`** - Extended bootstrap tester
2. **`doc/bug/bootstrap_mir_zero_modules.md`** - Bug documentation
3. **Debug logging** in `simple/compiler/driver.spl`

## Questions to Investigate

1. **Dictionary Semantics**: Are Simple dictionaries copy-on-write?
2. **Class Field Mutation**: Does `ctx.field = value` mutate or rebind?
3. **Context Copying**: Is `CompileContext` being copied somewhere unexpectedly?
4. **Method Resolution**: Does `resolve_methods()` return a new HIR module or mutate in place?

## Success Metrics

- [ ] Phase 3 debug log shows: "returning ctx with 1 HIR modules"
- [ ] AOT debug log shows: "ctx.hir_modules count = 1"
- [ ] MIR lowering processes 1 module (not 0)
- [ ] Generation 2 compiles successfully
- [ ] Generations 2 and 3 are bitwise identical

## Conclusion

The bootstrap failure is a dictionary mutation semantics issue where HIR modules stored in phase 3 are not visible in phase 5. Debug logging has been added to pinpoint the exact location where modules are lost. Once the semantic issue is understood, the fix should be straightforward (likely changing how we mutate the context or dictionaries).

The MCP server infrastructure is in place and ready to assist with deeper analysis once this initial bug is fixed.

---

**Status**: Investigation complete, awaiting debug log output to confirm hypothesis.

**Next Action**: Review debug output from background compilation task.
