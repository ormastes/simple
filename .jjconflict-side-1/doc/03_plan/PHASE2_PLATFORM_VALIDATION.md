# Phase 2: Platform & Validation Enhancements

**Date:** 2026-02-09
**Status:** 🚀 In Progress
**Follows:** Phase 1B (22 TODOs completed)

## Overview

Phase 2 focuses on platform detection, data validation, and utility functions that can be implemented in Pure Simple without FFI dependencies.

## Objectives

- **Platform Detection:** Implement host platform and architecture detection
- **Data Validation:** Add JSON and SQL validation logic
- **Utility Functions:** Template expansion, module detection, symbol resolution
- **Documentation:** Fill in empty TODO descriptions

## Sub-Phases

### Phase 2.1: Platform Detection (2 TODOs) 🔄

**File:** `src/compiler/smf_writer.spl`
**Dependencies:** `std.platform` (already exists)

**Tasks:**
1. **TODO #162:** Implement `Target.host()` using `std.platform.get_host_os()`
2. **Enhancement:** Add architecture detection to `std.platform`

**Deliverables:**
- Architecture detection: `get_host_arch()` returns "x86_64", "aarch64", "riscv64", etc.
- Updated `Target.host()` with proper OS and architecture

### Phase 2.2: Data Validation (2 TODOs)

**File:** `src/compiler/blocks/utils.spl`
**Dependencies:** None (Pure Simple)

**Tasks:**
1. **TODO #64:** Implement `validate_json_structure()`
   - Check for null/undefined values
   - Validate array homogeneity
   - Verify object structure
2. **TODO #65:** Implement `validate_sql_dialect()`
   - Common SQL keyword validation
   - PostgreSQL-specific checks
   - MySQL-specific checks
   - SQLite-specific checks

### Phase 2.3: Utility Functions (3 TODOs)

**Files:** `src/runtime/hooks.spl`, `src/lib/spec.spl`, `src/compiler/monomorphize_integration.spl`

**Tasks:**
1. **TODO #198:** Template variable replacement
   - Replace `{variable}` patterns with actual values
   - Handle escaping and missing variables
2. **TODO #211:** Module detection in spec framework
   - Detect if test is running in module context
   - Check for module-level before_each/after_each
3. **TODO #145:** Symbol name resolution
   - Convert symbol IDs to human-readable names
   - Format for error messages

### Phase 2.4: Documentation (8 TODOs)

**Fill in empty TODO descriptions:**
- #127: `src/compiler/module_resolver/manifest.spl` line 442
- #130: `src/compiler/module_resolver/resolution.spl` line 460
- #133: `src/compiler/module_resolver/types.spl` line 511
- #144: `src/compiler/monomorphize/hot_reload.spl` line 568
- #146: `src/compiler/monomorphize/metadata.spl` line 413
- #149: `src/compiler/monomorphize/partition.spl` line 615
- #150: `src/compiler/monomorphize/tracker.spl` line 506
- #152: `src/compiler/monomorphize/util.spl` line 502

## Implementation Strategy

1. **Platform First:** Easiest win, clear infrastructure exists
2. **Validation Next:** Self-contained logic, no dependencies
3. **Utilities:** Small helpers with clear use cases
4. **Documentation Last:** Fill in context after understanding code

## Success Criteria

- [ ] Platform detection works on Linux, macOS, Windows
- [ ] Architecture detection returns correct values
- [ ] JSON validation catches common errors
- [ ] SQL validation supports 3+ dialects
- [ ] Template replacement handles edge cases
- [ ] All 8 empty TODOs have descriptions
- [ ] All files compile successfully
- [ ] Test suite remains 330/330 passing

## Estimated TODOs Resolved

**Total:** 15 TODOs
- Platform: 2
- Validation: 2
- Utilities: 3
- Documentation: 8

## Timeline

- **Day 1:** Platform detection + architecture (Phase 2.1)
- **Day 2:** Data validation (Phase 2.2)
- **Day 3:** Utility functions (Phase 2.3)
- **Day 4:** Documentation + testing (Phase 2.4)

## Next Phase

**Phase 3:** Parser enhancements, type system improvements (20-30 TODOs)
