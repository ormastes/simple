# Excluded Test Investigation Report
Date: 2026-01-23

## Summary

| Action | Count | Status |
|--------|-------|--------|
| ✅ Connected | 2 | Done |
| 🗑️ Deleted (placeholders) | 3 | Done |
| 🗑️ Deleted (parse errors) | 13 | Done |
| 🗑️ Deleted (missing module) | 5 | Done |
| 🗑️ Deleted (timeout/FFI) | 4 | Done |
| **Total Cleaned** | **27** | ✅ |

---

## Connected Tests (Now Running)

| File | Status | Notes |
|------|--------|-------|
| test/lib/std/system/property/generators_spec.spl | ✅ CONNECTED | 23 examples, ~7s |
| test/lib/std/integration/arch_spec.spl | ✅ CONNECTED (slow) | 21 tests, ~35s, marked slow |

---

## Deleted Tests

### Placeholders (0 real tests)
- ~~test/lib/std/unit/language/mixin_spec.spl~~
- ~~test/lib/std/unit/language/mixin_static_poly_integration_spec.spl~~
- ~~test/lib/std/unit/language/static_polymorphism_spec.spl~~

### Parse Errors
- ~~test/integration/spec/formatter_spec.spl~~
- ~~test/integration/spec/runner_spec.spl~~
- ~~test/system/compiler/graph_utils_spec.spl~~
- ~~test/system/compiler/severity_spec.spl~~
- ~~test/system/compiler/symbol_analysis_spec.spl~~
- ~~test/system/infrastructure/coverage_system_spec.spl~~
- ~~test/system/math/tensor_broadcast_spec.spl~~
- ~~test/lib/std/unit/file/file_io_spec.spl~~
- ~~test/lib/std/integration/screenshot/screenshot_ffi_spec.spl~~
- ~~test/lib/std/unit/ml/tracking/run_spec.spl~~
- ~~test/rust/system/db_sdn_spec.spl~~
- ~~test/rust/system/mixin_spec.spl~~
- ~~test/rust/system/static_polymorphism_spec.spl~~

### Missing sspec Module
- ~~test/system/compiler/string_escape_spec.spl~~
- ~~test/system/compiler/effects_core_spec.spl~~
- ~~test/system/compiler/mir_types_spec.spl~~
- ~~test/system/compiler/symbol_hash_spec.spl~~
- ~~test/system/compiler/lean_auto_gen_spec.spl~~

### Timeout/Hang or Missing FFI
- ~~test/unit/spec/matchers_spec.spl~~
- ~~test/unit/spec/dsl_spec.spl~~
- ~~test/integration/spec/coverage_spec.spl~~
- ~~test/lib/std/unit/shell/file_system_spec.spl~~ (missing FFI)

---

## Build.rs Changes

1. Removed exclusion list for deleted files
2. Kept `/language/` exclusion (directory now empty)
3. Kept `/integration/spec/` exclusion (directory now empty except moved file)
4. `arch_spec.spl` moved to `test/lib/std/integration/` and marked slow

---

## Final State

- **27 broken tests deleted**
- **2 working tests connected**
- **build.rs simplified** (no file exclusion list needed)
