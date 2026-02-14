# Package Management Implementation

## Status: IN PROGRESS

## Problem
Tests for package management are timing out:
- `test/unit/app/package/semver_spec.spl` - TIMEOUT
- `test/unit/app/package/manifest_spec.spl` - TIMEOUT
- `test/unit/app/package/package_spec.spl` - TIMEOUT
- `test/unit/app/package/lockfile_spec.spl` - TIMEOUT
- `test/unit/app/package/ffi_spec.spl` - TIMEOUT

## Root Cause Analysis

### Issues Found

1. **Missing/Wrong Function Names in lockfile.spl**
   - Calls `parse_sdn()` but should call `parse_sdn_value()` from `app.sdn`
   - Calls `rt_timestamp_get_year/month/day/hour/minute/second()` but actual functions are `timestamp_year/month/day/hour/minute/second()` from `app.io.time_ops`
   - Line 329: Uses `.len()` on variables of unclear type

2. **Missing SDN Result Type Handling**
   - `parse_sdn()` doesn't exist - need to wrap `parse_sdn_value()` to return Result type
   - SDN parsing needs proper error handling

3. **Incomplete Manifest Parser**
   - `parse_manifest_string()` function is called by tests but not implemented
   - Need to parse SDN format with proper structure for package manifests

4. **Type Mismatches**
   - `SdnValue` operations in lockfile.spl don't match actual SDN API
   - Need to fix `impl SdnValue` extension methods

## Implementation Plan

### Phase 1: Fix Core Dependencies (CURRENT)
1. Add SDN wrapper function with Result type
2. Fix timestamp function calls in lockfile.spl
3. Add missing parse_manifest_string function
4. Fix SdnValue extensions

### Phase 2: Implement Manifest Parser
1. Parse package info section
2. Parse dependencies (registry, git, path)
3. Parse dev_dependencies
4. Validate manifest structure

### Phase 3: Test and Verify
1. Run semver_spec tests
2. Run manifest_spec tests
3. Run lockfile_spec tests
4. Run package_spec tests
5. Run ffi_spec tests

## Changes Made

### 2026-02-14

**Fixed Syntax Errors:**
1. Fixed inline if/then/else expressions in types.spl (lines 18-19) - rewrote as multi-line if blocks
2. Fixed enum field syntax in types.spl - changed from colon blocks to parentheses `Git(url:, ref:)`
3. Fixed all match expressions to use `case` keyword instead of bare pattern:
4. Replaced `?` operator (doesn't exist) with explicit Result handling pattern
5. Replaced `!` unwrap operator with `.unwrap()` method calls
6. Fixed timestamp function calls in lockfile.spl to use correct names

**Commented Out Incomplete Code:**
1. SDN parsing in lockfile.spl - needs proper SDN integration
2. SdnValue extension methods - incomplete
3. Complex table parsing - not yet ready

**Added Minimal Implementations:**
1. parse_manifest_string() with simple line-by-line parsing (temporary)
2. Exported manifest functions

**Remaining Issues:**
- semver.spl still has a parse error ("expected expression, found Newline") that prevents module from loading
- The runtime loads semver as empty dict {} instead of proper module
- Tests are marked @skip indicating they're not ready for implementation yet

**Current Status:**
- types.spl: COMPILES AND LOADS ✓
- semver.spl: PARSE ERROR - module loads as empty dict
- manifest.spl: COMPILES (minimal implementation)
- lockfile.spl: COMPILES (stub implementation)

The fundamental issue is that semver.spl has a subtle parse error that makes the entire module invalid. This could be:
- Result<T, E> generic syntax issue in interpreter
- Multi-line return statement parsing
- Function signature parsing with complex types

## Next Steps

1. Fix all function name mismatches
2. Implement manifest parser
3. Run tests to verify fixes
4. Iterate on failures

## Test Status

All tests are marked with `@skip` directive, indicating they are not ready for execution.

- semver_spec: BLOCKED - parse error in semver.spl prevents module loading
- manifest_spec: BLOCKED - depends on working semver module
- lockfile_spec: BLOCKED - depends on working semver module
- package_spec: BLOCKED - depends on all above modules
- ffi_spec: BLOCKED - depends on package infrastructure

## Recommendations

1. **Investigate semver.spl parse error** - The remaining parse error prevents the entire package management system from working. This should be highest priority.

2. **Consider simpler Result handling** - The current Result<T, E> pattern may not be fully supported in the interpreter. Consider using simpler error handling patterns.

3. **Incremental testing** - Build up from basic version parsing before tackling complex dependency resolution.

4. **SDN integration** - Proper SDN parsing support is needed for manifest and lockfile parsing.

## Code Files Modified

1. `/home/ormastes/dev/pub/simple/src/app/package/types.spl` - Fixed syntax errors
2. `/home/ormastes/dev/pub/simple/src/app/package/semver.spl` - Fixed most syntax, one parse error remains
3. `/home/ormastes/dev/pub/simple/src/app/package/manifest.spl` - Added parse_manifest_string stub
4. `/home/ormastes/dev/pub/simple/src/app/package/lockfile.spl` - Fixed imports, commented incomplete code
