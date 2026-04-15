# Failed Tests Recheck Report - 2026-01-24

## Summary

| Status | Count |
|--------|-------|
| Previously Failed | 14 |
| Now Passing | 6 |
| Now Ignored | 1 |
| Still Failing (parse errors) | 4 |
| Now Hanging | 3 |

---

## Test Results

### Now Passing (6 tests)

| Test | Duration | Examples |
|------|----------|----------|
| algorithm_utils_spec.spl | 0.01s | 33 |
| mock_spec.spl (test/lib/std/unit/spec) | 0.02s | 41 |
| progress_spec.spl | 0.01s | 14 |
| mock_spec.spl (simple/std_lib) | 314ms | 27 |
| math_spec.spl | 0.09s | 30 |

### Now Ignored (1 test)

| Test | Status |
|------|--------|
| resource_limited_spec.spl | IGNORED (marked with #[ignore]) |

### Still Failing - Parse Errors (4 tests)

| Test | Error |
|------|-------|
| helpers_spec.spl | `expected expression, found RParen` |
| mock_verification_spec.spl | `expected pattern, found Fn` |
| mock_phase3_spec.spl | `expected RParen, found Colon` |
| mock_phase4_spec.spl | `expected RParen, found Colon` |
| mock_phase5_spec.spl | `expected RParen, found Colon` |

### Now Hanging (3 tests)

| Test | Timeout |
|------|---------|
| set_spec.spl | >60s |
| mock_phase6_spec.spl | >60s |
| mock_phase7_spec.spl | >60s |

---

## Updated Totals

### Passing Tests
- Previously hanging: 12 now pass (math_spec moved here)
- Previously failing: 6 now pass
- **Total newly passing: 18 tests**

### Remaining Issues

| Category | Count | Files |
|----------|-------|-------|
| Parse Errors | 5 | helpers_spec, mock_verification_spec, mock_phase3-5_spec |
| Hanging | 3 | set_spec, mock_phase6_spec, mock_phase7_spec |
| Ignored | 1 | resource_limited_spec |
| **Total Issues** | **9** | |

---

## Recommendations

1. **Fix parse errors** in simple/std_lib/test/unit/testing/:
   - helpers_spec.spl - syntax issue
   - mock_verification_spec.spl - `fn` in unexpected position
   - mock_phase3-5_spec.spl - colon in wrong position

2. **Investigate hanging tests**:
   - set_spec.spl - Dict/Set operations may have infinite loop
   - mock_phase6_spec.spl - needs investigation
   - mock_phase7_spec.spl - needs investigation

3. **Review ignored test**:
   - resource_limited_spec.spl - check if should remain ignored

---

## Commands Used

```bash
# Rust test runner
timeout 60 cargo test -p simple-driver --test simple_stdlib_tests <test_name> -- --nocapture
timeout 60 cargo test -p simple-driver --test simple_tests <test_name> -- --nocapture

# Simple CLI
timeout 60 ./target/debug/simple test <path/to/spec.spl>
```
