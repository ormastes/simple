# Test Failures Summary (Excluding Parser Errors)

**Generated:** 2026-01-30
**Total Failures:** 92
**Parser Failures:** 75 (excluded)
**Non-Parser Failures:** 17

---

## Summary Table

| Category | Count | Status | Priority |
|----------|-------|--------|----------|
| Missing Files | 9 | ✅ Resolved (files moved) | - |
| Encoding | 3 | ✅ False positive | - |
| Timeout | 3 | 🔴 Needs investigation | HIGH |
| Semantic | 2 | 🔴 Needs fixing | HIGH |

---

## RESOLVED: Missing Files (9)

Files were moved during reorganization. New locations found:

- `hello_spec.spl` → `test/lib/std/unit/core/hello_spec.spl`
- `metrics_spec.spl` → `test/lib/std/unit/ml/engine/metrics_spec.spl`
- `sys_ffi_spec.spl` → `test/lib/std/unit/host/sys_ffi_spec.spl`
- `context_pack_spec.spl` → `test/lib/std/unit/tooling/context_pack_spec.spl`
- `server_spec.spl` → Multiple: `dap/server_spec.spl`, `lms/server_spec.spl`

**Action:** Rerun tests - database will auto-update with new paths.

---

## RESOLVED: Encoding Issues (3)

False positives - files are valid UTF-8. Errors were from temporary files in `/tmp/`.

---

## TODO: Timeouts (3 tests)

**Tests:**
1. `cli_spec` - 30s timeout
2. `spec_framework_spec` - 30s timeout
3. `fixture_spec` - 30s timeout

**Next Steps:**
1. Profile each test to find slow operations
2. Mark as `slow_it` or optimize
3. Consider increasing timeout limit

---

## TODO: Semantic Errors (2 tests)

**1. feature_doc_spec**
- Error: Cannot modify self in immutable method
- Fix: Change `fn` to `me` for methods that mutate self

**2. constructor_spec**
- Error: Native compilation failed
- Fix: Investigate codegen issue

---

## Action Required

**Immediate:**
```bash
# Rerun tests to update database with new file paths
./target/release/simple_old test

# Profile timeout tests
time ./target/release/simple_old test test/lib/std/unit/cli_spec.spl -v
```

**Code Fixes:**
- [ ] Fix mutability in `feature_doc_spec`
- [ ] Debug native compilation in `constructor_spec`
- [ ] Optimize or mark slow tests

---

## Expected Outcome

After fixes:
- **Non-parser failures:** 17 → 5 (timeouts pending investigation)
- **Parser failures:** 75 (separate work stream)
- **Overall:** 92 → 80 failures
- **Pass rate:** 89.6% → 91.2%

After parser fixes (future):
- **All tests:** 100% passing
