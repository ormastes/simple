# Test Failure Analysis - 2026-01-31

**Generated:** 2026-01-31
**Total Failed:** 45 tests (5.8%)
**Total Passed:** 728 tests (94.2%)

---

## Failure Categories

### Category 1: Parse Errors (15 tests)

**Root Cause:** Syntax issues in test files or imported modules

| Test | Error | Fix Needed |
|------|-------|------------|
| treesitter_tree_real_spec | Unexpected token: expected expression, found RBracket | Fix empty bracket syntax |
| treesitter_lexer_real_spec | Unexpected token: expected expression, found RBracket | Fix empty bracket syntax |
| treesitter_tokenkind_real_spec | Unexpected token: expected expression, found RBracket | Fix empty bracket syntax |
| treesitter_parser_real_spec | Unexpected token: expected expression, found RBracket | Fix empty bracket syntax |
| error_recovery_spec | expected Comma, found Assign | Fix parameter syntax |
| lexer_spec (sdn) | expected Fn, found Identifier "describe" | Import issue |
| generic_template_spec | expected expression, found Slash | Fix operator usage |
| command_dispatch_spec | expected expression, found Dot | Fix dot operator |

**Action:** Review and fix parse errors in these files.

---

### Category 2: Missing Test Functions (12 tests)

**Root Cause:** Tests using `skip_it`, `args`, `feature` without proper imports

| Test | Missing Function | Module |
|------|------------------|--------|
| generic_bytecode_spec | skip_it | std.spec |
| note_sdn_feature_spec | skip_it | std.spec |
| spec_matchers_spec | skip_it | std.spec |
| parser_improvements_spec | skip_it | std.spec |
| file_io_spec (sdn) | skip_it | std.spec |
| interpreter_bugs_spec | skip_it | std.spec |
| fault_detection_spec | args | std.env |
| lexer_ffi_test | args | std.env |
| error_recovery_simple_spec | feature | std.spec |

**Action:** Add proper imports or fix module resolution.

---

### Category 3: Upstream Parse Errors (10 tests)

**Root Cause:** Test files import modules that have parse errors

| Test | Failing Import | Parse Error |
|------|----------------|-------------|
| contact_spec | physics/collision/__init__.spl | expected identifier, found LBrace |
| shapes_spec | physics/collision/__init__.spl | expected identifier, found LBrace |
| spatial_hash_spec | physics/collision/__init__.spl | expected identifier, found LBrace |
| aabb_spec | physics/collision/__init__.spl | expected identifier, found LBrace |
| rigidbody_spec | physics/collision/__init__.spl | expected identifier, found LBrace |
| server_spec (lms) | lms/sys.spl | expected identifier, found LBrace |
| todo_parser_spec | tooling/core/project.spl | expected expression, found Newline |
| arg_parsing_spec | tooling/core/project.spl | expected expression, found Newline |
| note_sdn_spec | compiler/monomorphize/deferred.spl | expected expression, found Slash |
| note_sdn_bdd_spec | compiler/monomorphize/deferred.spl | expected expression, found Slash |

**Action:** Fix parse errors in imported modules first.

---

### Category 4: Semantic Errors (8 tests)

**Root Cause:** Type mismatches, trait coherence issues

| Test | Error | Issue |
|------|-------|-------|
| test_analysis_spec | type mismatch: cannot convert dict to int | Type error in code |
| context_pack_spec | OverlappingImpl { trait_name: "Add", type1: "text", type2: "text" } | Duplicate trait impl |
| file_io_spec (infra) | expected Fn, found DocComment | Doc comment placement |
| sys_ffi_spec | expected Colon, found Newline | Syntax error |
| datetime_spec | expected Colon, found Newline | Syntax error |
| filter_spec | expected pattern, found Val | Pattern match syntax |

**Action:** Fix semantic errors in each file.

---

## Priority Fixes

### P0 - High Impact (Fix Upstream Modules)

1. **physics/collision/__init__.spl** - Blocks 5 tests
2. **tooling/core/project.spl** - Blocks 4 tests
3. **compiler/monomorphize/deferred.spl** - Blocks 2 tests

### P1 - Medium Impact (Fix Imports)

4. Add missing `skip_it` imports to 7 test files
5. Add missing `args` function to 2 test files
6. Add missing `feature` function to 2 test files

### P2 - Low Impact (Individual Fixes)

7. Fix 15 individual parse errors
8. Fix 8 semantic errors

---

## Execution Summary

**Working:**
- ✅ Direct test execution: `simple_runtime file.spl`
- ✅ Interpreter mode: All 728 passing tests work
- ✅ FFI functions: All registered and callable

**Needs Work:**
- ⚠️ Test runner: Infinite recursion fixed, needs cache clear
- ⚠️ SMF mode: Not yet tested
- ❌ Native mode: Needs FFI bridge implementation

---

## Next Steps

1. Fix 3 upstream modules (P0)
2. Add missing imports (P1)
3. Fix individual parse/semantic errors (P2)
4. Implement native FFI bridge
5. Test SMF execution mode
