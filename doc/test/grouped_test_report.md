# Grouped Test Execution Report

Updated: 2026-01-24 (recheck completed)

## Summary

| Status | Count |
|--------|-------|
| **Total Directories Tested** | 25 |
| **Passed** | 284 files |
| **Failed** | 5 files |
| **Hanging (Timeout)** | 3 files |
| **Ignored** | 1 file |
| **Total Files** | 333 spec files |

---

## Test Groups Summary

| Group # | Category | Files | Status | Passed | Failed | Hang |
|---------|----------|-------|--------|--------|--------|------|
| 1 | test/lib/std/fixtures | 1 | PASS | 1 | 0 | 0 |
| 2 | test/lib/std/integration | 10 | PASS | 10 | 0 | 0 |
| 3 | test/lib/std/system | 34 | PASS | 34 | 0 | 0 |
| 4 | test/lib/std/unit/core | 22 | PASS | 22 | 0 | 0 |
| 5 | test/lib/std/unit/tooling | 50 | PASS | 50 | 0 | 0 |
| 6 | test/lib/std/unit/parser | 14 | PASS | 14 | 0 | 0 |
| 7 | test/lib/std/unit/ml | 13 | PASS | 13 | 0 | 0 |
| 8 | test/lib/std/unit/spec | 12 | PASS | 12 | 0 | 0 |
| 9 | test/lib/std/unit/game_engine | 9 | PASS | 9 | 0 | 0 |
| 10 | test/lib/std/unit/physics | 9 | PASS | 9 | 0 | 0 |
| 11 | test/lib/std/unit/ui | 8 | PASS | 8 | 0 | 0 |
| 12 | test/lib/std/unit/lsp | 7 | PASS | 7 | 0 | 0 |
| 13 | test/lib/std/unit/verification | 7 | PASS | 7 | 0 | 0 |
| 14 | test/lib/std/unit/sdn | 6 | PASS | 6 | 0 | 0 |
| 15 | test/lib/std/unit/concurrency | 5 | PASS | 5 | 0 | 0 |
| 16 | test/lib/std/unit/shell | 4 | PASS | 4 | 0 | 0 |
| 17 | test/lib/std/unit/misc | 12 | PASS | 12 | 0 | 0 |
| 18 | test/lib/std/unit/small | 9 | PASS | 9 | 0 | 0 |
| 19-22 | test/system/features | 72 | PASS | 72 | 0 | 0 |
| 23 | test/system/other | 22 | PASS | 22 | 0 | 0 |
| 24 | test/unit/spec | 3 | PASS | 3 | 0 | 0 |
| 25 | simple/std_lib | 16 | PARTIAL | 5 | 5 | 3 |

---

## Hanging Tests (Timeout > 60s)

| File | Directory |
|------|-----------|
| set_spec.spl | simple/std_lib/test/unit |
| mock_phase6_spec.spl | simple/std_lib/test/unit/testing |
| mock_phase7_spec.spl | simple/std_lib/test/unit/testing |

---

## Failed Tests (Parse Errors)

| File | Error |
|------|-------|
| helpers_spec.spl | `expected expression, found RParen` |
| mock_verification_spec.spl | `expected pattern, found Fn` |
| mock_phase3_spec.spl | `expected RParen, found Colon` |
| mock_phase4_spec.spl | `expected RParen, found Colon` |
| mock_phase5_spec.spl | `expected RParen, found Colon` |

All failed tests are in `simple/std_lib/test/unit/testing/` and have syntax errors.

---

## Ignored Tests

| File | Directory |
|------|-----------|
| resource_limited_spec.spl | test/lib/std/unit/spec |

---

## Passing Tests (Now Fixed)

These tests were previously failing or hanging but now pass:

| Test | Examples | Duration |
|------|----------|----------|
| algorithm_utils_spec.spl | 33 | 0.01s |
| mock_spec.spl (test/lib/std/unit/spec) | 41 | 0.02s |
| progress_spec.spl | 14 | 0.01s |
| mock_spec.spl (simple/std_lib) | 27 | 314ms |
| math_spec.spl | 30 | 0.09s |
| arch_spec.spl | 27 | 0.36s |
| json_spec.spl | 16 | 0.01s |
| math_ffi_spec.spl | 20 | 0.01s |
| string_literals_spec.spl | 25 | 0.04s |
| string_spec.spl | 46 | 2.11s |
| lean_codegen_spec.spl | 13 | 0.01s |
| naming_spec.spl | 28 | 0.03s |
| memory_capabilities_spec.spl | 23 | 0.01s |
| regeneration_spec.spl | 10 | 0.00s |
| registry_spec.spl | 14 | 0.01s |
| expect_spec.spl | 21 | 0.01s |
| map_spec.spl | 16 | 13ms |
| contract_spec.spl | 22 | 53ms |
| smoke_test_spec.spl | 22 | 28ms |

---

## Recommendations

1. **Fix parse errors** in simple/std_lib/test/unit/testing/:
   - Check syntax in helpers_spec.spl, mock_verification_spec.spl, mock_phase3-5_spec.spl

2. **Investigate hanging tests**:
   - set_spec.spl - Dict/Set operations
   - mock_phase6_spec.spl, mock_phase7_spec.spl - mock framework

3. **All other directories are safe** to run without issues

---

## Running Tests

```bash
# Safe to run (all pass)
./target/debug/simple test test/lib/std/
./target/debug/simple test test/system/
./target/debug/simple test test/unit/spec

# Has issues (simple/std_lib)
# Skip: set_spec, mock_phase6_spec, mock_phase7_spec, helpers_spec, mock_verification_spec, mock_phase3-5_spec
```

---

## History

- **2026-01-24 (recheck)**: 6 previously failed tests now pass, 3 hanging identified in simple/std_lib
- **2026-01-24**: All 13 original hanging tests resolved
- **2026-01-23**: Initial report (13 hanging, 16 failed)
