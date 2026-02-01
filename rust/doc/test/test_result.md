# Test Results

**Generated:** 2026-02-01 11:36:23
**Total Tests:** 1148
**Status:** ⚠️ 251 FAILED

## Summary

| Status | Count | Percentage |
|--------|-------|-----------|
| ✅ Passed | 897 | 78.1% |
| ❌ Failed | 251 | 21.9% |
| ⏭️ Skipped | 0 | 0.0% |
| 🔕 Ignored | 0 | 0.0% |
| 🔐 Qualified Ignore | 0 | 0.0% |

---

## ❌ Failed Tests (251)

### 🔴 metaprogramming_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/metaprogramming_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.217946214+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Colon
Location: /home/ormastes/dev/pub/simple/test/specs/metaprogramming_spec.spl
```

---

### 🔴 mock_simple_spec

**File:** `test/lib/std/unit/spec/mock_simple_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.734320011+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/spec/mock_simple_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/spec/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/spec/mock_simple_spec.spl
```

---

### 🔴 minimal_spec

**File:** `test/system/features/database_synchronization/minimal_spec.spl`
**Category:** System
**Failed:** 2026-02-01T07:57:01.746932140+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/system/features/database_synchronization/minimal_spec.spl) [export_outside_init]
  --> line 250, column 1
  = help: move this export to ../test/system/features/database_synchronization/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/database_synchronization/minimal_spec.spl) [export_outside_init]
  --> line 251, column 1
  = help: move this export to ../test/system/features/database_synchronization/__init__.spl (the directory manifest)

Location: ../test/system/features/database_synchronization/minimal_spec.spl
```

---

### 🔴 mock_direct_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_direct_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.209363777+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 707, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 709, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 710, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 711, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 712, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 713, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 714, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 715, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 716, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 717, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 718, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 719, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 720, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_direct_spec.spl
```

---

### 🔴 linker_context_spec

**File:** `test/lib/std/unit/compiler/linker_context_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.721410573+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: function arguments: expected Comma, found Colon
Location: ../test/lib/std/unit/compiler/linker_context_spec.spl
```

---

### 🔴 lexer_ffi_test

**File:** `test/lib/std/compiler/lexer_ffi_test.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.716854160+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/core/traits.spl": Unexpected token: expected identifier, found Into
Location: ../test/lib/std/compiler/lexer_ffi_test.spl
```

---

### 🔴 parser_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/parser_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.208585763+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/parser_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/parser_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/parser_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/parser_spec.spl
```

---

### 🔴 rigidbody_spec

**File:** `test/lib/std/unit/physics/dynamics/rigidbody_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.733238934+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 40, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 40, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 43, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 51, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 80, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 81, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 82, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 83, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 84, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 85, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 86, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 87, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 88, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 89, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 90, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 91, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 52, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 55, column 1
  = help: move this export to ../test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/physics/dynamics/rigidbody_spec.spl
```

---

### 🔴 process_spec

**File:** `test/lib/std/unit/shell/process_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.733945104+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/shell/process_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/shell/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/shell/process_spec.spl
```

---

### 🔴 test_meta_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/spec/test_meta_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.209832331+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/test_meta_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/test_meta_spec.spl
```

---

### 🔴 lexer_spec

**File:** `test/lib/std/unit/sdn/lexer_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.733430300+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Fn, found Identifier { name: "describe", pattern: Immutable }
Location: ../test/lib/std/unit/sdn/lexer_spec.spl
```

---

### 🔴 static_polymorphism_spec

**File:** `test/system/static_polymorphism_spec.spl`
**Category:** System
**Failed:** 2026-02-01T07:57:01.755236531+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Impl
Location: ../test/system/static_polymorphism_spec.spl
```

---

### 🔴 data_structures_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/data_structures_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.217676128+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Let, found Struct
Location: /home/ormastes/dev/pub/simple/test/specs/data_structures_spec.spl
```

---

### 🔴 test_integration_spec

**File:** `home/ormastes/dev/pub/simple/test/build/test_integration_spec.spl`
**Category:** Integration
**Failed:** 2026-02-01T08:48:13.189663486+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `TestConfig` not found
Location: /home/ormastes/dev/pub/simple/test/build/test_integration_spec.spl
```

---

### 🔴 block_skip_policy_spec

**File:** `test/compiler/blocks/block_skip_policy_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.716447502+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 316, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 317, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 318, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 319, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 320, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 321, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 417, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 418, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 419, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 420, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 421, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 12, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 13, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 14, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 16, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 17, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 18, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 22, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 23, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 27, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 28, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 32, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 33, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 34, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 37, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 38, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 45, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 46, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 47, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 88, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 89, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 51, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 52, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 53, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 56, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 57, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 58, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 59, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 62, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 63, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 64, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 69, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 70, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 66, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 76, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 77, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 78, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 170, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 171, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 161, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 162, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 163, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 164, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 165, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 101, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 102, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 431, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 432, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 433, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 434, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 435, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 525, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 526, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 527, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 528, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 529, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 530, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 531, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 532, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 533, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 519, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 520, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 133, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 134, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 198, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 199, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 166, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 167, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 335, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 81, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 84, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 85, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

Location: ../test/compiler/blocks/block_skip_policy_spec.spl
```

---

### 🔴 file_find_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/shell/file_find_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.208943004+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/file_find_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/file_find_spec.spl
```

---

### 🔴 capability_effects_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/capability_effects_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.217542173+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Colon
Location: /home/ormastes/dev/pub/simple/test/specs/capability_effects_spec.spl
```

---

### 🔴 test_ffi_operator_spec

**File:** `test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.731181950+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 123, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 124, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 125, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 126, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 127, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 128, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 129, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 330, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 331, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 332, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 333, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 334, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 335, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 336, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 337, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 338, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 339, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 340, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 341, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 342, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 343, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 344, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 345, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 346, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 347, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 348, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl
```

---

### 🔴 advanced_spec

**File:** `test/build/advanced_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.715077142+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `BuildMetrics` not found
Location: ../test/build/advanced_spec.spl
```

---

### 🔴 feature_doc_spec

**File:** `test/lib/std/system/feature_doc_spec.spl`
**Category:** System
**Failed:** 2026-02-01T07:57:01.717343516+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 487, column 1
  = help: move this export to ../test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 488, column 1
  = help: move this export to ../test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 491, column 1
  = help: move this export to ../test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 492, column 1
  = help: move this export to ../test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 493, column 1
  = help: move this export to ../test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 494, column 1
  = help: move this export to ../test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 495, column 1
  = help: move this export to ../test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 496, column 1
  = help: move this export to ../test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 497, column 1
  = help: move this export to ../test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 498, column 1
  = help: move this export to ../test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 499, column 1
  = help: move this export to ../test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 500, column 1
  = help: move this export to ../test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 501, column 1
  = help: move this export to ../test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 502, column 1
  = help: move this export to ../test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 503, column 1
  = help: move this export to ../test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 504, column 1
  = help: move this export to ../test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 505, column 1
  = help: move this export to ../test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 506, column 1
  = help: move this export to ../test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 507, column 1
  = help: move this export to ../test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 508, column 1
  = help: move this export to ../test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 509, column 1
  = help: move this export to ../test/lib/std/system/__init__.spl (the directory manifest)

Location: ../test/lib/std/system/feature_doc_spec.spl
```

---

### 🔴 regex_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/core/regex_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.198503534+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/core/regex_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/core/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/core/regex_spec.spl
```

---

### 🔴 todo_parser_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/todo_tests/todo_parser_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.210109410+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/todo_tests/todo_parser_spec.spl
```

---

### 🔴 pre_lex_per_dsl_spec

**File:** `home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.190903613+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 316, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 317, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 318, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 319, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 320, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 321, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 417, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 418, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 419, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 420, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 421, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 12, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 13, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 14, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 16, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 17, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 18, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 22, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 23, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 27, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 28, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 32, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 33, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 34, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 37, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 38, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 45, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 46, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 47, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 88, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 89, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 51, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 52, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 53, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 56, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 57, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 58, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 59, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 62, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 63, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 64, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 69, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 70, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 66, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 76, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 77, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 78, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 170, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 171, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 161, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 162, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 163, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 164, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 165, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 101, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 102, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 431, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 432, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 433, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 434, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 435, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 525, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 526, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 527, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 528, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 529, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 530, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 531, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 532, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 533, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 519, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 520, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 133, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 134, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 198, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 199, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 166, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 167, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 335, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 81, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 84, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 85, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl
```

---

### 🔴 static_polymorphism_spec

**File:** `home/ormastes/dev/pub/simple/test/system/static_polymorphism_spec.spl`
**Category:** System
**Failed:** 2026-02-01T08:48:13.231757498+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Impl
Location: /home/ormastes/dev/pub/simple/test/system/static_polymorphism_spec.spl
```

---

### 🔴 mcp_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.204088060+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 399, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 400, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 401, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 402, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 403, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 404, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 405, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 406, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 4, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 4, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 6, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 10, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 11, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 6, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 36, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 37, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 44, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 47, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 31, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 53, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 389, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 56, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 7, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 705, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 706, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 707, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 708, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 709, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 710, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 711, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 712, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 10, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 11, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl
```

---

### 🔴 type_inference_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/type_inference_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.218400160+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Val
Location: /home/ormastes/dev/pub/simple/test/specs/type_inference_spec.spl
```

---

### 🔴 component_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/component_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.199883137+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/component_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/component_spec.spl
```

---

### 🔴 scene_node_spec

**File:** `test/system/features/game_engine/scene_node_spec.spl`
**Category:** System
**Failed:** 2026-02-01T07:57:01.748385630+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/system/features/game_engine/scene_node_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/system/features/game_engine/__init__.spl (the directory manifest)

Location: ../test/system/features/game_engine/scene_node_spec.spl
```

---

### 🔴 mixin_spec

**File:** `home/ormastes/dev/pub/simple/test/system/mixin_spec.spl`
**Category:** System
**Failed:** 2026-02-01T08:48:13.231609355+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found Pass
Location: /home/ormastes/dev/pub/simple/test/system/mixin_spec.spl
```

---

### 🔴 static_method_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/codegen/static_method_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.195749539+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `feature` not found
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/codegen/static_method_spec.spl
```

---

### 🔴 tensor_bridge_spec

**File:** `test/system/features/math/tensor_bridge_spec.spl`
**Category:** System
**Failed:** 2026-02-01T07:57:01.749709351+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/system/features/math/tensor_bridge_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/system/features/math/__init__.spl (the directory manifest)

Location: ../test/system/features/math/tensor_bridge_spec.spl
```

---

### 🔴 config_loader_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/config/config_loader_spec.spl`
**Category:** System
**Failed:** 2026-02-01T08:48:13.221467233+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/config/config_loader_spec.spl) [export_outside_init]
  --> line 579, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/config/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/config/config_loader_spec.spl) [export_outside_init]
  --> line 580, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/config/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/config/config_loader_spec.spl) [export_outside_init]
  --> line 581, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/config/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/system/features/config/config_loader_spec.spl
```

---

### 🔴 quat_spec

**File:** `test/system/features/math/quat_spec.spl`
**Category:** System
**Failed:** 2026-02-01T07:57:01.749639487+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/system/features/math/quat_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/system/features/math/__init__.spl (the directory manifest)

Location: ../test/system/features/math/quat_spec.spl
```

---

### 🔴 spatial_hash_spec

**File:** `test/lib/std/unit/physics/collision/spatial_hash_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.733048219+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 3, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 40, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 40, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 43, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 51, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 80, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 81, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 82, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 83, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 84, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 85, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 86, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 87, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 88, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 89, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 90, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 91, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 52, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 55, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/physics/collision/spatial_hash_spec.spl
```

---

### 🔴 block_skip_policy_spec

**File:** `home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.190728779+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 316, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 317, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 318, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 319, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 320, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 321, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 417, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 418, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 419, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 420, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 421, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 12, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 13, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 14, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 16, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 17, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 18, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 22, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 23, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 27, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 28, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 32, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 33, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 34, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 37, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 38, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 45, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 46, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 47, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 88, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 89, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 51, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 52, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 53, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 56, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 57, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 58, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 59, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 62, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 63, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 64, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 69, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 70, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 66, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 76, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 77, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 78, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 170, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 171, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 161, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 162, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 163, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 164, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 165, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 101, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 102, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 431, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 432, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 433, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 434, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 435, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 525, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 526, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 527, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 528, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 529, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 530, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 531, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 532, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 533, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 519, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 520, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 133, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 134, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 198, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 199, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 166, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 167, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 335, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 81, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 84, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl) [export_outside_init]
  --> line 85, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl
```

---

### 🔴 db_sdn_spec

**File:** `home/ormastes/dev/pub/simple/test/system/db_sdn_spec.spl`
**Category:** System
**Failed:** 2026-02-01T08:48:13.219187252+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected fn, struct, class, enum, union, impl, mod, extern, or pub after attributes, found Identifier { name: "describe", pattern: Immutable }
Location: /home/ormastes/dev/pub/simple/test/system/db_sdn_spec.spl
```

---

### 🔴 error_handler_spec

**File:** `test/lib/std/unit/mcp/error_handler_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.728145102+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/error_handler_spec.spl) [export_outside_init]
  --> line 4, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/error_handler_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/error_handler_spec.spl) [export_outside_init]
  --> line 6, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/error_handler_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/error_handler_spec.spl) [export_outside_init]
  --> line 10, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/error_handler_spec.spl) [export_outside_init]
  --> line 11, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/mcp/error_handler_spec.spl
```

---

### 🔴 command_dispatch_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/command_dispatch_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.212933078+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Dot
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/command_dispatch_spec.spl
```

---

### 🔴 minimal_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/database_synchronization/minimal_spec.spl`
**Category:** System
**Failed:** 2026-02-01T08:48:13.222268131+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/database_synchronization/minimal_spec.spl) [export_outside_init]
  --> line 250, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/database_synchronization/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/database_synchronization/minimal_spec.spl) [export_outside_init]
  --> line 251, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/database_synchronization/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/system/features/database_synchronization/minimal_spec.spl
```

---

### 🔴 value_spec

**File:** `test/lib/std/unit/sdn/value_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.733685688+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/value_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/value_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/value_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/sdn/value_spec.spl
```

---

### 🔴 todo_parser_spec

**File:** `test/lib/std/unit/tooling/todo_parser_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.738204700+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: ../test/lib/std/unit/tooling/todo_parser_spec.spl
```

---

### 🔴 arg_parsing_spec

**File:** `test/lib/std/unit/tooling/arg_parsing_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.735002306+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: ../test/lib/std/unit/tooling/arg_parsing_spec.spl
```

---

### 🔴 logger_spec

**File:** `test/lib/std/unit/mcp/logger_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.728458442+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/logger_spec.spl) [export_outside_init]
  --> line 4, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/logger_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/logger_spec.spl) [export_outside_init]
  --> line 6, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/logger_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/logger_spec.spl) [export_outside_init]
  --> line 10, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/logger_spec.spl) [export_outside_init]
  --> line 11, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/mcp/logger_spec.spl
```

---

### 🔴 env_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/shell/env_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.208871107+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/env_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/env_spec.spl
```

---

### 🔴 test_db_validation_spec

**File:** `test/lib/std/unit/tooling/test_db_validation_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.737956495+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: ../test/lib/std/unit/tooling/test_db_validation_spec.spl
```

---

### 🔴 spatial_hash_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.208090468+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 3, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 40, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 40, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 43, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 51, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 80, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 81, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 82, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 83, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 84, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 85, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 86, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 87, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 88, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 89, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 90, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 91, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 52, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl) [export_outside_init]
  --> line 55, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl
```

---

### 🔴 error_handler_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/error_handler_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.203393856+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/error_handler_spec.spl) [export_outside_init]
  --> line 4, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/error_handler_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/error_handler_spec.spl) [export_outside_init]
  --> line 6, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/error_handler_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/error_handler_spec.spl) [export_outside_init]
  --> line 10, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/error_handler_spec.spl) [export_outside_init]
  --> line 11, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/error_handler_spec.spl
```

---

### 🔴 random_spec

**File:** `test/lib/std/unit/core/random_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.723680454+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/core/random_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to ../test/lib/std/unit/core/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/core/random_spec.spl
```

---

### 🔴 random_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/core/random_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.198434964+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/core/random_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/core/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/core/random_spec.spl
```

---

### 🔴 actor_model_spec

**File:** `test/system/features/game_engine/actor_model_spec.spl`
**Category:** System
**Failed:** 2026-02-01T07:57:01.748246754+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Actor
Location: ../test/system/features/game_engine/actor_model_spec.spl
```

---

### 🔴 test_meta_spec

**File:** `test/lib/std/unit/spec/test_meta_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.734624924+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/spec/test_meta_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/spec/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/spec/test_meta_spec.spl
```

---

### 🔴 export_syntax_spec

**File:** `test/lib/std/unit/mcp/export_syntax_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.728208544+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/export_syntax_spec.spl) [export_outside_init]
  --> line 4, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/export_syntax_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/export_syntax_spec.spl) [export_outside_init]
  --> line 6, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/export_syntax_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/export_syntax_spec.spl) [export_outside_init]
  --> line 10, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/export_syntax_spec.spl) [export_outside_init]
  --> line 11, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/mcp/export_syntax_spec.spl
```

---

### 🔴 types_spec

**File:** `test/specs/types_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.740547340+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Let, found Struct
Location: ../test/specs/types_spec.spl
```

---

### 🔴 mixin_comprehensive_test

**File:** `home/ormastes/dev/pub/simple/test/integration/mixin_comprehensive_test.simple`
**Category:** Integration
**Failed:** 2026-02-01T08:48:13.190980840+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Colon, found Newline
Location: /home/ormastes/dev/pub/simple/test/integration/mixin_comprehensive_test.simple
```

---

### 🔴 instruction_coverage_spec

**File:** `test/compiler/backend/instruction_coverage_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.715803932+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Vec
Location: ../test/compiler/backend/instruction_coverage_spec.spl
```

---

### 🔴 simple_math_integration_spec

**File:** `test/lib/std/unit/ml/simple_math_integration_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.730503853+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/ml/simple_math_integration_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/ml/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/ml/simple_math_integration_spec.spl
```

---

### 🔴 treesitter_parser_real_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_parser_real_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.207352730+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RBracket
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_parser_real_spec.spl
```

---

### 🔴 test_db_integrity_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/test_db_integrity_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.215747438+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/test_db_integrity_spec.spl
```

---

### 🔴 actor_model_spec

**File:** `test/lib/std/unit/game_engine/actor_model_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.724791539+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/lib/std/unit/game_engine/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/game_engine/actor_model_spec.spl
```

---

### 🔴 fault_detection_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl`
**Category:** System
**Failed:** 2026-02-01T08:48:13.223087655+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 316, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 317, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 318, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 319, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 320, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 321, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 417, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 418, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 419, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 420, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 421, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 12, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 13, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 14, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 16, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 17, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 18, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 22, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 23, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 27, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 28, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 32, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 33, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 34, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 37, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 38, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 45, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 46, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 47, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 88, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 89, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 51, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 52, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 53, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 56, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 57, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 58, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 59, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 62, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 63, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 64, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 69, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 70, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 66, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 76, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 77, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 78, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 170, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 171, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 161, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 162, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 163, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 164, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 165, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 101, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 102, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 431, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 432, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 433, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 434, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 435, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 525, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 526, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 527, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 528, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 529, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 530, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 531, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 532, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 533, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 519, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 520, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 133, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 134, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 198, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 199, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 166, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 167, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 335, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 81, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 84, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 85, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/fault_detection/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl
```

---

### 🔴 time_spec

**File:** `test/lib/std/unit/core/time_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.723999234+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/core/time_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/core/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/core/time_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to ../test/lib/std/unit/core/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/core/time_spec.spl
```

---

### 🔴 aabb_spec

**File:** `test/lib/std/unit/physics/collision/aabb_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.732714130+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 40, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 40, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 43, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 51, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 80, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 81, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 82, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 83, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 84, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 85, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 86, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 87, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 88, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 89, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 90, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 91, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 52, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 55, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/physics/collision/aabb_spec.spl
```

---

### 🔴 query_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/query_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.208653772+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 36, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 37, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 44, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 47, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 31, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 53, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 389, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 56, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/query_spec.spl
```

---

### 🔴 comment_only_spec

**File:** `home/ormastes/dev/pub/simple/rust/test/meta/comment_only_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-31T09:32:37.751992043+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `group_stack` not found
Location: /home/ormastes/dev/pub/simple/rust/test/meta/comment_only_spec.spl
```

---

### 🔴 import_test

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/import_test.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.213998080+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/import_test.spl
```

---

### 🔴 synchronization_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/core/synchronization_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.198707283+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/core/synchronization_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/core/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/core/synchronization_spec.spl
```

---

### 🔴 macro_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/macro_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.217806167+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `test` not found
Location: /home/ormastes/dev/pub/simple/test/specs/macro_spec.spl
```

---

### 🔴 context_manager_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/core/context_manager_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.197416039+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/core/context_manager_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/core/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/core/context_manager_spec.spl) [export_outside_init]
  --> line 184, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/core/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/core/context_manager_spec.spl
```

---

### 🔴 suspension_operator_spec

**File:** `test/specs/suspension_operator_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.740302612+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pointcut expression 'pc{...}', found LParen
Location: ../test/specs/suspension_operator_spec.spl
```

---

### 🔴 type_inference_spec

**File:** `test/specs/type_inference_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.740486554+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Val
Location: ../test/specs/type_inference_spec.spl
```

---

### 🔴 memory_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/memory_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.217878174+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RParen
Location: /home/ormastes/dev/pub/simple/test/specs/memory_spec.spl
```

---

### 🔴 jit_context_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/jit_context_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.196043661+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: function arguments: expected Comma, found Colon
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/jit_context_spec.spl
```

---

### 🔴 native_ffi_spec

**File:** `test/compiler/backend/native_ffi_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.716148090+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `slow_it` not found
Location: ../test/compiler/backend/native_ffi_spec.spl
```

---

### 🔴 file_io_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/system/sdn/file_io_spec.spl`
**Category:** System
**Failed:** 2026-02-01T08:48:13.193324382+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/sdn/file_io_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/sdn/file_io_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/sdn/file_io_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/sdn/file_io_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/sdn/file_io_spec.spl) [export_outside_init]
  --> line 31, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/sdn/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/system/sdn/file_io_spec.spl
```

---

### 🔴 treesitter_parser_real_spec

**File:** `test/lib/std/unit/parser/treesitter_parser_real_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.732395330+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RBracket
Location: ../test/lib/std/unit/parser/treesitter_parser_real_spec.spl
```

---

### 🔴 server_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/lms/server_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.201394932+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/lms/sys.spl": Unexpected token: expected identifier, found LBrace
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/lms/server_spec.spl
```

---

### 🔴 backend_capability_spec

**File:** `test/compiler/backend/backend_capability_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.715588099+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Vec
Location: ../test/compiler/backend/backend_capability_spec.spl
```

---

### 🔴 treesitter_lexer_real_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_lexer_real_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.207210569+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RBracket
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_lexer_real_spec.spl
```

---

### 🔴 basic_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/fs/basic_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.199598824+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/fs/basic_spec.spl) [export_outside_init]
  --> line 260, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/fs/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/fs/basic_spec.spl) [export_outside_init]
  --> line 261, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/fs/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/fs/basic_spec.spl) [export_outside_init]
  --> line 262, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/fs/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/fs/basic_spec.spl) [export_outside_init]
  --> line 263, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/fs/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/fs/basic_spec.spl) [export_outside_init]
  --> line 264, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/fs/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/fs/basic_spec.spl) [export_outside_init]
  --> line 7, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/fs/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/fs/basic_spec.spl
```

---

### 🔴 materials_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/materials_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.207937947+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/materials_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/materials_spec.spl
```

---

### 🔴 syntax_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/syntax_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.218270613+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Indent
Location: /home/ormastes/dev/pub/simple/test/specs/syntax_spec.spl
```

---

### 🔴 vector_spec

**File:** `test/lib/std/unit/physics/core/vector_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.733172466+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/core/vector_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/lib/std/unit/physics/core/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/core/vector_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to ../test/lib/std/unit/physics/core/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/physics/core/vector_spec.spl
```

---

### 🔴 simple_math_integration_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/ml/simple_math_integration_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.205270296+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/simple_math_integration_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/simple_math_integration_spec.spl
```

---

### 🔴 contact_spec

**File:** `test/lib/std/unit/physics/collision/contact_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T10:27:30.915605736+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
failed to read test/lib/std/unit/physics/collision/contact_spec.spl: No such file or directory (os error 2)
Location: test/lib/std/unit/physics/collision/contact_spec.spl
```

---

### 🔴 time_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/core/time_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.198774632+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/core/time_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/core/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/core/time_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/core/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/core/time_spec.spl
```

---

### 🔴 generic_template_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/generic_template_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.195972515+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Slash
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/generic_template_spec.spl
```

---

### 🔴 roundtrip_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/roundtrip_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.208727323+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/roundtrip_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/roundtrip_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/roundtrip_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/roundtrip_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/roundtrip_spec.spl
```

---

### 🔴 shapes_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.208014322+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 40, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 40, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 43, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 51, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 80, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 81, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 82, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 83, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 84, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 85, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 86, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 87, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 88, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 89, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 90, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 91, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 52, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 55, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl
```

---

### 🔴 quality_spec

**File:** `test/build/quality_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.715386393+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `LintConfig` not found
Location: ../test/build/quality_spec.spl
```

---

### 🔴 contact_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.207787079+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 32, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 40, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 40, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 43, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 51, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 80, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 81, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 82, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 83, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 84, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 85, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 86, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 87, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 88, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 89, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 90, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 91, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 52, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 55, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl
```

---

### 🔴 mixin_comprehensive_test

**File:** `test/integration/mixin_comprehensive_test.simple`
**Category:** Integration
**Failed:** 2026-02-01T07:57:01.716660019+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Colon, found Newline
Location: ../test/integration/mixin_comprehensive_test.simple
```

---

### 🔴 linker_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/linker_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.196250355+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/core/traits.spl": Unexpected token: expected identifier, found Into
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/linker_spec.spl
```

---

### 🔴 fixed_size_edge_cases_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/arrays/fixed_size_edge_cases_spec.spl`
**Category:** System
**Failed:** 2026-02-01T02:35:55.934809639+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Slice
Location: /home/ormastes/dev/pub/simple/test/system/features/arrays/fixed_size_edge_cases_spec.spl
```

---

### 🔴 file_find_spec

**File:** `test/lib/std/unit/shell/file_find_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.733811739+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/shell/file_find_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/shell/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/shell/file_find_spec.spl
```

---

### 🔴 exhaustiveness_validator_spec

**File:** `test/compiler/backend/exhaustiveness_validator_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.715731523+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: function arguments: expected Comma, found Colon
Location: ../test/compiler/backend/exhaustiveness_validator_spec.spl
```

---

### 🔴 arg_parsing_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/arg_parsing_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.210248435+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/arg_parsing_spec.spl
```

---

### 🔴 roundtrip_spec

**File:** `test/lib/std/unit/sdn/roundtrip_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.733624591+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/roundtrip_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/roundtrip_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/roundtrip_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/roundtrip_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/sdn/roundtrip_spec.spl
```

---

### 🔴 feature_doc_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl`
**Category:** System
**Failed:** 2026-02-01T08:48:13.191742223+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 487, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 488, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 491, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 492, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 493, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 494, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 495, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 496, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 497, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 498, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 499, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 500, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 501, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 502, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 503, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 504, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 505, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 506, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 507, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 508, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl) [export_outside_init]
  --> line 509, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl
```

---

### 🔴 db_sdn_spec

**File:** `test/system/db_sdn_spec.spl`
**Category:** System
**Failed:** 2026-02-01T07:57:01.741255975+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected fn, struct, class, enum, union, impl, mod, extern, or pub after attributes, found Identifier { name: "describe", pattern: Immutable }
Location: ../test/system/db_sdn_spec.spl
```

---

### 🔴 actor_model_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/game_engine/actor_model_spec.spl`
**Category:** System
**Failed:** 2026-02-01T08:48:13.223804983+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Actor
Location: /home/ormastes/dev/pub/simple/test/system/features/game_engine/actor_model_spec.spl
```

---

### 🔴 decorators_spec

**File:** `test/lib/std/unit/core/decorators_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.723014501+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/core/decorators_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to ../test/lib/std/unit/core/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/core/decorators_spec.spl
```

---

### 🔴 decorators_comprehensive_spec

**File:** `test/lib/std/unit/core/decorators_comprehensive_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T09:34:32.886848436+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
failed to read test/lib/std/unit/core/decorators_comprehensive_spec.spl: No such file or directory (os error 2)
Location: test/lib/std/unit/core/decorators_comprehensive_spec.spl
```

---

### 🔴 mat4_spec

**File:** `test/system/features/math/mat4_spec.spl`
**Category:** System
**Failed:** 2026-02-01T07:57:01.749574553+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/system/features/math/mat4_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/system/features/math/__init__.spl (the directory manifest)

Location: ../test/system/features/math/mat4_spec.spl
```

---

### 🔴 symbol_table_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.204774089+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 399, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 400, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 401, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 402, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 403, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 404, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 405, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 406, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 4, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 4, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 6, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 10, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 11, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 6, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 36, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 37, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 44, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 47, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 31, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 53, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 389, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 56, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 7, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 705, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 706, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 707, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 708, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 709, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 710, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 711, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 712, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 10, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 11, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl
```

---

### 🔴 document_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/document_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.208449833+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/document_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/document_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/document_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/document_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/document_spec.spl) [export_outside_init]
  --> line 31, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/document_spec.spl
```

---

### 🔴 aabb_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.207711414+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 40, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 40, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 43, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 51, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 80, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 81, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 82, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 83, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 84, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 85, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 86, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 87, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 88, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 89, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 90, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 91, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 52, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl) [export_outside_init]
  --> line 55, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl
```

---

### 🔴 block_outline_info_spec

**File:** `test/compiler/blocks/block_outline_info_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.716373200+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 316, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 317, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 318, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 319, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 320, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 321, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 417, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 418, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 419, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 420, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 421, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 12, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 13, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 14, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 16, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 17, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 18, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 22, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 23, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 27, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 28, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 32, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 33, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 34, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 37, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 38, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 45, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 46, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 47, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 88, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 89, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 51, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 52, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 53, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 56, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 57, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 58, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 59, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 62, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 63, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 64, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 69, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 70, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 66, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 76, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 77, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 78, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 170, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 171, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 161, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 162, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 163, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 164, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 165, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 101, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 102, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 431, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 432, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 433, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 434, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 435, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 525, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 526, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 527, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 528, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 529, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 530, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 531, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 532, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 533, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 519, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 520, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 133, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 134, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 198, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 199, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 166, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 167, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 335, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 81, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 84, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 85, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

Location: ../test/compiler/blocks/block_outline_info_spec.spl
```

---

### 🔴 vector_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/physics/core/vector_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.208231677+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/core/vector_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/core/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/core/vector_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/core/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/core/vector_spec.spl
```

---

### 🔴 error_recovery_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/parser/error_recovery_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.206385875+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: function arguments: expected Comma, found Assign
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/parser/error_recovery_spec.spl
```

---

### 🔴 mixin_spec

**File:** `test/system/mixin_spec.spl`
**Category:** System
**Failed:** 2026-02-01T07:57:01.755108406+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found Pass
Location: ../test/system/mixin_spec.spl
```

---

### 🔴 dependencies_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.203187753+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 399, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 400, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 401, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 402, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 403, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 404, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 405, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 406, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 4, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 4, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 6, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 10, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 11, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 6, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 36, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 37, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 44, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 47, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 31, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 53, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 389, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 56, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 7, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 705, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 706, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 707, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 708, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 709, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 710, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 711, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 712, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 10, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 11, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl
```

---

### 🔴 context_pack_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/context_pack_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.213140183+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/core/traits.spl": Unexpected token: expected identifier, found Into
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/context_pack_spec.spl
```

---

### 🔴 backend_capability_spec

**File:** `home/ormastes/dev/pub/simple/test/compiler/backend/backend_capability_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.189820145+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Vec
Location: /home/ormastes/dev/pub/simple/test/compiler/backend/backend_capability_spec.spl
```

---

### 🔴 regex_utils_spec

**File:** `test/lib/std/unit/tooling/regex_utils_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:12:42.237911445+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
failed to read test/lib/std/unit/tooling/regex_utils_spec.spl: No such file or directory (os error 2)
Location: test/lib/std/unit/tooling/regex_utils_spec.spl
```

---

### 🔴 functions_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/functions_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.217742255+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found LParen
Location: /home/ormastes/dev/pub/simple/test/specs/functions_spec.spl
```

---

### 🔴 compatibility_spec

**File:** `test/lib/std/unit/sdn/compatibility_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.733303297+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/compatibility_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/compatibility_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/compatibility_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/compatibility_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/sdn/compatibility_spec.spl
```

---

### 🔴 error_recovery_simple_spec

**File:** `test/lib/std/unit/parser/error_recovery_simple_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.731431247+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `feature` not found
Location: ../test/lib/std/unit/parser/error_recovery_simple_spec.spl
```

---

### 🔴 todo_parser_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/todo_parser_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.216070946+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/todo_parser_spec.spl
```

---

### 🔴 file_io_spec

**File:** `test/lib/std/system/sdn/file_io_spec.spl`
**Category:** System
**Failed:** 2026-02-01T07:57:01.718848634+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/sdn/file_io_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to ../test/lib/std/system/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/sdn/file_io_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to ../test/lib/std/system/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/sdn/file_io_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to ../test/lib/std/system/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/sdn/file_io_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to ../test/lib/std/system/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/sdn/file_io_spec.spl) [export_outside_init]
  --> line 31, column 1
  = help: move this export to ../test/lib/std/system/sdn/__init__.spl (the directory manifest)

Location: ../test/lib/std/system/sdn/file_io_spec.spl
```

---

### 🔴 fault_detection_spec

**File:** `test/system/features/fault_detection/fault_detection_spec.spl`
**Category:** System
**Failed:** 2026-02-01T07:57:01.747613764+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 316, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 317, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 318, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 319, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 320, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 321, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 417, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 418, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 419, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 420, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 421, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 12, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 13, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 14, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 16, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 17, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 18, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 22, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 23, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 27, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 28, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 32, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 33, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 34, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 37, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 38, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 45, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 46, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 47, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 88, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 89, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 51, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 52, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 53, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 56, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 57, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 58, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 59, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 62, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 63, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 64, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 69, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 70, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 66, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 76, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 77, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 78, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 170, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 171, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 161, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 162, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 163, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 164, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 165, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 101, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 102, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 431, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 432, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 433, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 434, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 435, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 525, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 526, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 527, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 528, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 529, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 530, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 531, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 532, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 533, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 519, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 520, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 133, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 134, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 198, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 199, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 166, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 167, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 335, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 81, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 84, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/fault_detection/fault_detection_spec.spl) [export_outside_init]
  --> line 85, column 1
  = help: move this export to ../test/system/features/fault_detection/__init__.spl (the directory manifest)

Location: ../test/system/features/fault_detection/fault_detection_spec.spl
```

---

### 🔴 component_spec

**File:** `test/system/features/game_engine/component_spec.spl`
**Category:** System
**Failed:** 2026-02-01T07:57:01.748316037+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/game_engine/effects.spl": Unexpected token: expected expression, found Dot
Location: ../test/system/features/game_engine/component_spec.spl
```

---

### 🔴 linker_spec

**File:** `test/lib/std/unit/compiler/linker_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.721473253+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/core/traits.spl": Unexpected token: expected identifier, found Into
Location: ../test/lib/std/unit/compiler/linker_spec.spl
```

---

### 🔴 command_dispatch_spec

**File:** `test/lib/std/unit/tooling/command_dispatch_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.735305025+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Dot
Location: ../test/lib/std/unit/tooling/command_dispatch_spec.spl
```

---

### 🔴 datetime_ffi_spec

**File:** `test/lib/std/unit/host/datetime_ffi_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.725653768+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/host/datetime_ffi_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/host/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/host/datetime_ffi_spec.spl
```

---

### 🔴 syntax_spec

**File:** `test/specs/syntax_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.740362797+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Indent
Location: ../test/specs/syntax_spec.spl
```

---

### 🔴 metaprogramming_spec

**File:** `test/specs/metaprogramming_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.740055149+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Colon
Location: ../test/specs/metaprogramming_spec.spl
```

---

### 🔴 scene_node_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/game_engine/scene_node_spec.spl`
**Category:** System
**Failed:** 2026-02-01T08:48:13.223980007+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/game_engine/scene_node_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/game_engine/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/system/features/game_engine/scene_node_spec.spl
```

---

### 🔴 test_audio_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/test_audio_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.200293500+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/test_audio_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/test_audio_spec.spl
```

---

### 🔴 mcp_spec

**File:** `test/lib/std/unit/mcp/mcp_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.728760128+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 399, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 400, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 401, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 402, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 403, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 404, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 405, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 406, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 4, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 4, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 6, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 10, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 11, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 6, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 36, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 37, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 44, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 47, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 31, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 53, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 389, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 56, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 7, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 705, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 706, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 707, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 708, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 709, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 710, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 711, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 712, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 10, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/mcp_spec.spl) [export_outside_init]
  --> line 11, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/mcp/mcp_spec.spl
```

---

### 🔴 bdd_timeout_minimal_spec

**File:** `test/lib/std/system/spec/bdd_timeout_minimal_spec.spl`
**Category:** System
**Failed:** 2026-02-01T07:57:01.719137156+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/system/spec/bdd_timeout_minimal_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to ../test/lib/std/system/spec/__init__.spl (the directory manifest)

Location: ../test/lib/std/system/spec/bdd_timeout_minimal_spec.spl
```

---

### 🔴 materials_spec

**File:** `test/lib/std/unit/physics/collision/materials_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.732915355+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/materials_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/physics/collision/materials_spec.spl
```

---

### 🔴 lexer_ffi_test

**File:** `home/ormastes/dev/pub/simple/test/lib/std/compiler/lexer_ffi_test.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.191199978+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/core/traits.spl": Unexpected token: expected identifier, found Into
Location: /home/ormastes/dev/pub/simple/test/lib/std/compiler/lexer_ffi_test.spl
```

---

### 🔴 process_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/shell/process_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.209081038+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/process_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/process_spec.spl
```

---

### 🔴 package_spec

**File:** `test/build/package_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.715325497+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `PackageType` not found
Location: ../test/build/package_spec.spl
```

---

### 🔴 async_default_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/async_default_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.217474003+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Ellipsis
Location: /home/ormastes/dev/pub/simple/test/specs/async_default_spec.spl
```

---

### 🔴 types_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/types_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.218463220+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Let, found Struct
Location: /home/ormastes/dev/pub/simple/test/specs/types_spec.spl
```

---

### 🔴 failure_analysis_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.203540105+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 36, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 37, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 44, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 47, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 31, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 53, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 389, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 56, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 4, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 6, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 10, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 11, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl
```

---

### 🔴 vec3_spec

**File:** `test/system/features/math/vec3_spec.spl`
**Category:** System
**Failed:** 2026-02-01T07:57:01.749842145+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/system/features/math/vec3_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/system/features/math/__init__.spl (the directory manifest)

Location: ../test/system/features/math/vec3_spec.spl
```

---

### 🔴 error_recovery_simple_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/parser/error_recovery_simple_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.206312796+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `feature` not found
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/parser/error_recovery_simple_spec.spl
```

---

### 🔴 macro_spec

**File:** `test/specs/macro_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.739929599+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `test` not found
Location: ../test/specs/macro_spec.spl
```

---

### 🔴 filter_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/diagram/filter_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.199531235+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/diagram/recorder.spl": Unexpected token: expected pattern, found Val
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/diagram/filter_spec.spl
```

---

### 🔴 import_test

**File:** `test/lib/std/unit/tooling/import_test.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.736294707+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: ../test/lib/std/unit/tooling/import_test.spl
```

---

### 🔴 value_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/value_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.208795423+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/value_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/value_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/value_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/value_spec.spl
```

---

### 🔴 mock_simple_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_simple_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.209507542+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_simple_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_simple_spec.spl
```

---

### 🔴 memory_spec

**File:** `test/specs/memory_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.739989703+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RParen
Location: ../test/specs/memory_spec.spl
```

---

### 🔴 basic_spec

**File:** `test/lib/std/unit/fs/basic_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.724727326+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/fs/basic_spec.spl) [export_outside_init]
  --> line 260, column 1
  = help: move this export to ../test/lib/std/unit/fs/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/fs/basic_spec.spl) [export_outside_init]
  --> line 261, column 1
  = help: move this export to ../test/lib/std/unit/fs/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/fs/basic_spec.spl) [export_outside_init]
  --> line 262, column 1
  = help: move this export to ../test/lib/std/unit/fs/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/fs/basic_spec.spl) [export_outside_init]
  --> line 263, column 1
  = help: move this export to ../test/lib/std/unit/fs/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/fs/basic_spec.spl) [export_outside_init]
  --> line 264, column 1
  = help: move this export to ../test/lib/std/unit/fs/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/fs/basic_spec.spl) [export_outside_init]
  --> line 7, column 1
  = help: move this export to ../test/lib/std/unit/fs/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/fs/basic_spec.spl
```

---

### 🔴 mock_direct_spec

**File:** `test/lib/std/unit/spec/mock_direct_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.734193699+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 707, column 1
  = help: move this export to ../test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 709, column 1
  = help: move this export to ../test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 710, column 1
  = help: move this export to ../test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 711, column 1
  = help: move this export to ../test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 712, column 1
  = help: move this export to ../test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 713, column 1
  = help: move this export to ../test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 714, column 1
  = help: move this export to ../test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 715, column 1
  = help: move this export to ../test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 716, column 1
  = help: move this export to ../test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 717, column 1
  = help: move this export to ../test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 718, column 1
  = help: move this export to ../test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 719, column 1
  = help: move this export to ../test/lib/std/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
  --> line 720, column 1
  = help: move this export to ../test/lib/std/unit/spec/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/spec/mock_direct_spec.spl
```

---

### 🔴 context_pack_spec

**File:** `test/lib/std/unit/tooling/context_pack_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.735489217+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/core/traits.spl": Unexpected token: expected identifier, found Into
Location: ../test/lib/std/unit/tooling/context_pack_spec.spl
```

---

### 🔴 type_conversion_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/arrays/type_conversion_spec.spl`
**Category:** System
**Failed:** 2026-02-01T02:35:55.935152775+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected indented block after ':', found Identifier { name: "it", pattern: Immutable }
Location: /home/ormastes/dev/pub/simple/test/system/features/arrays/type_conversion_spec.spl
```

---

### 🔴 concurrency_spec

**File:** `test/specs/concurrency_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.739730788+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Case
Location: ../test/specs/concurrency_spec.spl
```

---

### 🔴 actor_model_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/actor_model_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.199670541+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/actor_model_spec.spl
```

---

### 🔴 server_spec

**File:** `test/lib/std/unit/lms/server_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.726346713+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/lms/sys.spl": Unexpected token: expected identifier, found LBrace
Location: ../test/lib/std/unit/lms/server_spec.spl
```

---

### 🔴 test_integration_spec

**File:** `test/build/test_integration_spec.spl`
**Category:** Integration
**Failed:** 2026-02-01T07:57:01.715450065+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `TestConfig` not found
Location: ../test/build/test_integration_spec.spl
```

---

### 🔴 decorators_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/core/decorators_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.197689982+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/core/decorators_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/core/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/core/decorators_spec.spl
```

---

### 🔴 test_audio_spec

**File:** `test/lib/std/unit/game_engine/test_audio_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.725349837+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/game_engine/test_audio_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/lib/std/unit/game_engine/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/game_engine/test_audio_spec.spl
```

---

### 🔴 transform_spec

**File:** `test/system/features/math/transform_spec.spl`
**Category:** System
**Failed:** 2026-02-01T07:57:01.749776970+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/system/features/math/transform_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/system/features/math/__init__.spl (the directory manifest)

Location: ../test/system/features/math/transform_spec.spl
```

---

### 🔴 class_method_call_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/class_method_call_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.201326731+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 316, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 317, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 318, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 319, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 320, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 321, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 417, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 418, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 419, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 420, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 421, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/class_method_call_spec.spl
```

---

### 🔴 codegen_parity_completion_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/codegen_parity_completion/codegen_parity_completion_spec.spl`
**Category:** System
**Failed:** 2026-02-01T08:48:13.220919538+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found By
Location: /home/ormastes/dev/pub/simple/test/system/features/codegen_parity_completion/codegen_parity_completion_spec.spl
```

---

### 🔴 modules_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/modules_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.218010557+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `test` not found
Location: /home/ormastes/dev/pub/simple/test/specs/modules_spec.spl
```

---

### 🔴 sys_ffi_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/host/sys_ffi_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.200768366+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/host/common/io/term_types.spl": Unexpected token: expected Colon, found Newline
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/host/sys_ffi_spec.spl
```

---

### 🔴 synchronization_spec

**File:** `test/lib/std/unit/core/synchronization_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.723937155+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/core/synchronization_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to ../test/lib/std/unit/core/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/core/synchronization_spec.spl
```

---

### 🔴 pass_unit_equivalence_spec

**File:** `test/system/features/control_flow/pass_unit_equivalence_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.746699305+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Val
Location: ../test/system/features/control_flow/pass_unit_equivalence_spec.spl
```

---

### 🔴 transport_edge_cases_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/transport_edge_cases_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.204848121+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/transport_edge_cases_spec.spl) [export_outside_init]
  --> line 4, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/transport_edge_cases_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/transport_edge_cases_spec.spl) [export_outside_init]
  --> line 6, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/transport_edge_cases_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/transport_edge_cases_spec.spl) [export_outside_init]
  --> line 10, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/transport_edge_cases_spec.spl) [export_outside_init]
  --> line 11, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/transport_edge_cases_spec.spl
```

---

### 🔴 failure_analysis_spec

**File:** `test/lib/std/unit/mcp/failure_analysis_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.728273818+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 36, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 37, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 44, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 47, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 31, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 53, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 389, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 56, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 4, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 6, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 10, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/failure_analysis_spec.spl) [export_outside_init]
  --> line 11, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/mcp/failure_analysis_spec.spl
```

---

### 🔴 data_structures_spec

**File:** `test/specs/data_structures_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.739796334+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Let, found Struct
Location: ../test/specs/data_structures_spec.spl
```

---

### 🔴 fixed_size_arrays_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/arrays/fixed_size_arrays_spec.spl`
**Category:** System
**Failed:** 2026-02-01T02:35:55.934721841+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected indented block after ':', found Context
Location: /home/ormastes/dev/pub/simple/test/system/features/arrays/fixed_size_arrays_spec.spl
```

---

### 🔴 env_spec

**File:** `test/lib/std/unit/shell/env_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.733748097+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/shell/env_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/shell/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/shell/env_spec.spl
```

---

### 🔴 dependencies_spec

**File:** `test/lib/std/unit/mcp/dependencies_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.727958746+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 399, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 400, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 401, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 402, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 403, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 404, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 405, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 406, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 4, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 4, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 6, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 10, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 11, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 6, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 36, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 37, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 44, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 47, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 31, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 53, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 389, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 56, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 7, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 705, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 706, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 707, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 708, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 709, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 710, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 711, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 712, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 10, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/dependencies_spec.spl) [export_outside_init]
  --> line 11, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/mcp/dependencies_spec.spl
```

---

### 🔴 regex_spec

**File:** `test/lib/std/unit/core/regex_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.723741110+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/core/regex_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to ../test/lib/std/unit/core/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/core/regex_spec.spl
```

---

### 🔴 mock_recorder_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_recorder_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.209435685+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_recorder_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_recorder_spec.spl
```

---

### 🔴 bootstrap_spec

**File:** `test/build/bootstrap_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.715140974+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `BootstrapStage` not found
Location: ../test/build/bootstrap_spec.spl
```

---

### 🔴 config_loader_spec

**File:** `test/system/features/config/config_loader_spec.spl`
**Category:** System
**Failed:** 2026-02-01T07:57:01.746233644+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/system/features/config/config_loader_spec.spl) [export_outside_init]
  --> line 579, column 1
  = help: move this export to ../test/system/features/config/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/config/config_loader_spec.spl) [export_outside_init]
  --> line 580, column 1
  = help: move this export to ../test/system/features/config/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/system/features/config/config_loader_spec.spl) [export_outside_init]
  --> line 581, column 1
  = help: move this export to ../test/system/features/config/__init__.spl (the directory manifest)

Location: ../test/system/features/config/config_loader_spec.spl
```

---

### 🔴 test_analysis_spec

**File:** `test/app/test_analysis_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:59:33.699429741+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
failed to read test/app/test_analysis_spec.spl: No such file or directory (os error 2)
Location: test/app/test_analysis_spec.spl
```

---

### 🔴 class_method_call_spec

**File:** `test/lib/std/unit/interpreter/class_method_call_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.726285446+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 316, column 1
  = help: move this export to ../test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 317, column 1
  = help: move this export to ../test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 318, column 1
  = help: move this export to ../test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 319, column 1
  = help: move this export to ../test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 320, column 1
  = help: move this export to ../test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 321, column 1
  = help: move this export to ../test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 417, column 1
  = help: move this export to ../test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 418, column 1
  = help: move this export to ../test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 419, column 1
  = help: move this export to ../test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 420, column 1
  = help: move this export to ../test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/interpreter/class_method_call_spec.spl) [export_outside_init]
  --> line 421, column 1
  = help: move this export to ../test/lib/std/unit/interpreter/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/interpreter/class_method_call_spec.spl
```

---

### 🔴 differential_testing_spec

**File:** `test/compiler/backend/differential_testing_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.715659245+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Error("Invalid integer: 9223372036854775808")
Location: ../test/compiler/backend/differential_testing_spec.spl
```

---

### 🔴 document_spec

**File:** `test/lib/std/unit/sdn/document_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.733366528+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/document_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/document_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/document_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/document_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/document_spec.spl) [export_outside_init]
  --> line 31, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/sdn/document_spec.spl
```

---

### 🔴 query_spec

**File:** `test/lib/std/unit/sdn/query_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.733560478+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 36, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 37, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 44, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 47, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 31, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 53, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 389, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/query_spec.spl) [export_outside_init]
  --> line 56, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/sdn/query_spec.spl
```

---

### 🔴 shapes_spec

**File:** `test/lib/std/unit/physics/collision/shapes_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.732981601+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 40, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 40, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 43, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 51, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 80, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 81, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 82, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 83, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 84, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 85, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 86, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 87, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 88, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 89, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 90, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 91, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 52, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/physics/collision/shapes_spec.spl) [export_outside_init]
  --> line 55, column 1
  = help: move this export to ../test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/physics/collision/shapes_spec.spl
```

---

### 🔴 pre_lex_per_dsl_spec

**File:** `test/compiler/blocks/pre_lex_per_dsl_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.716593301+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 316, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 317, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 318, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 319, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 320, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 321, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 417, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 418, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 419, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 420, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 421, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 12, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 13, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 14, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 16, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 17, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 18, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 22, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 23, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 27, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 28, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 32, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 33, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 34, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 37, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 38, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 45, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 46, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 47, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 88, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 89, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 51, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 52, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 53, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 56, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 57, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 58, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 59, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 62, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 63, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 64, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 69, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 70, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 66, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 76, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 77, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 78, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 170, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 171, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 161, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 162, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 163, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 164, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 165, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 101, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 102, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 431, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 432, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 433, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 434, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 435, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 525, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 526, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 527, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 528, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 529, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 530, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 531, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 532, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 533, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 519, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 520, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 133, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 134, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 198, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 199, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 166, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 167, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 335, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 81, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 84, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_per_dsl_spec.spl) [export_outside_init]
  --> line 85, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

Location: ../test/compiler/blocks/pre_lex_per_dsl_spec.spl
```

---

### 🔴 advanced_spec

**File:** `home/ormastes/dev/pub/simple/test/build/advanced_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.189228697+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `BuildMetrics` not found
Location: /home/ormastes/dev/pub/simple/test/build/advanced_spec.spl
```

---

### 🔴 pre_lex_info_spec

**File:** `home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.190810665+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 316, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 317, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 318, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 319, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 320, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 321, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 417, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 418, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 419, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 420, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 421, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 12, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 13, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 14, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 16, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 17, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 18, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 22, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 23, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 27, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 28, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 32, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 33, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 34, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 37, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 38, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 45, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 46, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 47, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 88, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 89, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 51, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 52, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 53, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 56, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 57, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 58, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 59, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 62, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 63, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 64, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 69, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 70, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 66, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 76, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 77, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 78, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 170, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 171, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 161, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 162, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 163, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 164, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 165, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 101, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 102, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 431, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 432, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 433, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 434, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 435, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 525, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 526, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 527, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 528, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 529, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 530, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 531, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 532, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 533, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 519, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 520, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 133, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 134, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 198, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 199, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 166, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 167, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 335, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 81, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 84, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 85, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl
```

---

### 🔴 concurrency_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/concurrency_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.217608820+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Case
Location: /home/ormastes/dev/pub/simple/test/specs/concurrency_spec.spl
```

---

### 🔴 rigidbody_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.208306169+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 40, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 40, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 43, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 51, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 80, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 81, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 82, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 83, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 84, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 85, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 86, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 87, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 88, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 89, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 90, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 91, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 52, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 55, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl
```

---

### 🔴 parser_spec

**File:** `test/lib/std/unit/sdn/parser_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.733491627+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/parser_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/parser_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/sdn/parser_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to ../test/lib/std/unit/sdn/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/sdn/parser_spec.spl
```

---

### 🔴 error_recovery_spec

**File:** `test/lib/std/unit/parser/error_recovery_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.731494978+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: function arguments: expected Comma, found Assign
Location: ../test/lib/std/unit/parser/error_recovery_spec.spl
```

---

### 🔴 tensor_bridge_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/math/tensor_bridge_spec.spl`
**Category:** System
**Failed:** 2026-02-01T04:24:13.075696350+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Flat
Location: /home/ormastes/dev/pub/simple/test/system/features/math/tensor_bridge_spec.spl
```

---

### 🔴 cargo_spec

**File:** `home/ormastes/dev/pub/simple/test/build/cargo_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.189375096+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `BuildConfig` not found
Location: /home/ormastes/dev/pub/simple/test/build/cargo_spec.spl
```

---

### 🔴 mock_recorder_spec

**File:** `test/lib/std/unit/spec/mock_recorder_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.734256319+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/spec/mock_recorder_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/spec/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/spec/mock_recorder_spec.spl
```

---

### 🔴 functions_spec

**File:** `test/specs/functions_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.739858693+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found LParen
Location: ../test/specs/functions_spec.spl
```

---

### 🔴 transport_edge_cases_spec

**File:** `test/lib/std/unit/mcp/transport_edge_cases_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.730133855+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/transport_edge_cases_spec.spl) [export_outside_init]
  --> line 4, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/transport_edge_cases_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/transport_edge_cases_spec.spl) [export_outside_init]
  --> line 6, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/transport_edge_cases_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/transport_edge_cases_spec.spl) [export_outside_init]
  --> line 10, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/transport_edge_cases_spec.spl) [export_outside_init]
  --> line 11, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/mcp/transport_edge_cases_spec.spl
```

---

### 🔴 path_spec

**File:** `test/lib/std/unit/shell/path_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.733881462+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/shell/path_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/shell/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/shell/path_spec.spl
```

---

### 🔴 symbol_table_spec

**File:** `test/lib/std/unit/mcp/symbol_table_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.730065745+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 399, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 400, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 401, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 402, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 403, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 404, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 405, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 406, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 4, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 4, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 6, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 10, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 11, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 6, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 36, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 37, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 44, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 47, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 31, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 53, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 389, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 56, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 7, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 705, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 706, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 707, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 708, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 709, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 710, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 711, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 712, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 10, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/mcp/symbol_table_spec.spl) [export_outside_init]
  --> line 11, column 1
  = help: move this export to ../test/lib/std/unit/mcp/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/mcp/symbol_table_spec.spl
```

---

### 🔴 cargo_spec

**File:** `test/build/cargo_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.715201920+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `BuildConfig` not found
Location: ../test/build/cargo_spec.spl
```

---

### 🔴 block_definition_three_level_spec

**File:** `test/compiler/blocks/block_definition_three_level_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.716298648+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 316, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 317, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 318, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 319, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 320, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 321, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 417, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 418, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 419, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 420, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 421, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 12, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 13, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 14, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 16, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 17, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 18, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 22, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 23, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 27, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 28, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 32, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 33, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 34, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 37, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 38, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 45, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 46, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 47, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 88, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 89, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 51, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 52, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 53, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 56, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 57, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 58, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 59, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 62, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 63, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 64, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 69, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 70, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 66, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 76, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 77, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 78, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 170, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 171, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 161, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 162, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 163, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 164, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 165, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 101, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 102, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 431, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 432, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 433, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 434, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 435, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 525, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 526, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 527, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 528, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 529, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 530, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 531, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 532, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 533, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 519, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 520, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 133, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 134, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 198, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 199, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 166, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 167, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 335, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 81, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 84, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 85, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

Location: ../test/compiler/blocks/block_definition_three_level_spec.spl
```

---

### 🔴 codegen_parity_completion_spec

**File:** `test/system/features/codegen_parity_completion/codegen_parity_completion_spec.spl`
**Category:** System
**Failed:** 2026-02-01T07:57:01.745737686+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found By
Location: ../test/system/features/codegen_parity_completion/codegen_parity_completion_spec.spl
```

---

### 🔴 filter_spec

**File:** `test/lib/std/unit/diagram/filter_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.724663945+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/diagram/recorder.spl": Unexpected token: expected pattern, found Val
Location: ../test/lib/std/unit/diagram/filter_spec.spl
```

---

### 🔴 suspension_operator_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/suspension_operator_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.218206831+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pointcut expression 'pc{...}', found LParen
Location: /home/ormastes/dev/pub/simple/test/specs/suspension_operator_spec.spl
```

---

### 🔴 treesitter_tokenkind_real_spec

**File:** `test/lib/std/unit/parser/treesitter_tokenkind_real_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.732582749+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RBracket
Location: ../test/lib/std/unit/parser/treesitter_tokenkind_real_spec.spl
```

---

### 🔴 todo_parser_spec

**File:** `test/lib/std/unit/todo_tests/todo_parser_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.734877136+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: ../test/lib/std/unit/todo_tests/todo_parser_spec.spl
```

---

### 🔴 exhaustiveness_validator_spec

**File:** `home/ormastes/dev/pub/simple/test/compiler/backend/exhaustiveness_validator_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.189996101+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: function arguments: expected Comma, found Colon
Location: /home/ormastes/dev/pub/simple/test/compiler/backend/exhaustiveness_validator_spec.spl
```

---

### 🔴 shell_api_spec

**File:** `test/specs/shell_api_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.740236495+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Syntax error at 107:17: Cannot use 'exists' as a function name.

'exists' is a reserved keyword for existential quantifiers in verification:
Example: exists x in range: predicate

To check file/path existence, use 'exist' instead:
- file.exist(path)   # In shell module
- path.exist(path)   # In shell module
- file_exist(path)   # In infra module

Suggestion: Replace 'exists' with 'exist'
Location: ../test/specs/shell_api_spec.spl
```

---

### 🔴 test_db_validation_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/test_db_validation_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.215812653+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/test_db_validation_spec.spl
```

---

### 🔴 block_definition_three_level_spec

**File:** `home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.190560338+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 316, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 317, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 318, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 319, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 320, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 321, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 417, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 418, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 419, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 420, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 421, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 12, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 13, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 14, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 16, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 17, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 18, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 22, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 23, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 27, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 28, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 32, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 33, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 34, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 37, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 38, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 45, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 46, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 47, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 88, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 89, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 51, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 52, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 53, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 56, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 57, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 58, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 59, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 62, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 63, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 64, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 69, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 70, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 66, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 76, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 77, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 78, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 170, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 171, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 161, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 162, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 163, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 164, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 165, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 101, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 102, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 431, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 432, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 433, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 434, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 435, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 525, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 526, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 527, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 528, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 529, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 530, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 531, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 532, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 533, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 519, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 520, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 133, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 134, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 198, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 199, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 166, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 167, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 335, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 81, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 84, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl) [export_outside_init]
  --> line 85, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl
```

---

### 🔴 instruction_coverage_spec

**File:** `home/ormastes/dev/pub/simple/test/compiler/backend/instruction_coverage_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.190079129+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Vec
Location: /home/ormastes/dev/pub/simple/test/compiler/backend/instruction_coverage_spec.spl
```

---

### 🔴 coverage_spec

**File:** `test/build/coverage_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.715263758+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `CoverageLevel` not found
Location: ../test/build/coverage_spec.spl
```

---

### 🔴 progress_timing_test

**File:** `test/unit/spec/progress_timing_test.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.755592702+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/unit/spec/progress_timing_test.spl) [export_outside_init]
  --> line 101, column 1
  = help: move this export to ../test/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/unit/spec/progress_timing_test.spl) [export_outside_init]
  --> line 102, column 1
  = help: move this export to ../test/unit/spec/__init__.spl (the directory manifest)

Location: ../test/unit/spec/progress_timing_test.spl
```

---

### 🔴 jit_context_spec

**File:** `test/lib/std/unit/compiler/jit_context_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.721285584+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: function arguments: expected Comma, found Colon
Location: ../test/lib/std/unit/compiler/jit_context_spec.spl
```

---

### 🔴 file_io_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/infra/file_io_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.201252790+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/infra/alloc.spl": Unexpected token: expected identifier, found Minus
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/infra/file_io_spec.spl
```

---

### 🔴 static_method_spec

**File:** `test/lib/std/unit/codegen/static_method_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.721025477+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `feature` not found
Location: ../test/lib/std/unit/codegen/static_method_spec.spl
```

---

### 🔴 async_default_spec

**File:** `test/specs/async_default_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.739603625+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Ellipsis
Location: ../test/specs/async_default_spec.spl
```

---

### 🔴 mat4_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/math/mat4_spec.spl`
**Category:** System
**Failed:** 2026-02-01T04:24:13.075531565+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `group_stack` not found
Location: /home/ormastes/dev/pub/simple/test/system/features/math/mat4_spec.spl
```

---

### 🔴 pre_lex_info_spec

**File:** `test/compiler/blocks/pre_lex_info_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.716519750+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 316, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 317, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 318, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 319, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 320, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 321, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 417, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 418, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 419, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 420, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 421, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 12, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 13, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 14, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 16, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 17, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 18, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 22, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 23, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 27, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 28, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 32, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 33, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 34, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 37, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 38, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 45, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 46, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 47, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 88, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 89, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 51, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 52, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 53, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 56, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 57, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 58, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 59, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 62, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 63, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 64, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 69, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 70, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 66, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 76, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 77, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 78, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 170, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 171, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 161, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 162, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 163, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 164, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 165, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 101, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 102, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 431, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 432, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 433, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 434, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 435, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 525, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 526, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 527, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 528, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 529, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 530, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 531, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 532, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 533, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 519, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 520, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 133, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 134, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 198, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 199, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 166, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 167, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 335, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 81, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 84, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/compiler/blocks/pre_lex_info_spec.spl) [export_outside_init]
  --> line 85, column 1
  = help: move this export to ../test/compiler/blocks/__init__.spl (the directory manifest)

Location: ../test/compiler/blocks/pre_lex_info_spec.spl
```

---

### 🔴 datetime_ffi_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/host/datetime_ffi_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.200630062+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/host/datetime_ffi_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/host/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/host/datetime_ffi_spec.spl
```

---

### 🔴 file_io_spec

**File:** `test/lib/std/unit/infra/file_io_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.726217206+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/infra/alloc.spl": Unexpected token: expected identifier, found Minus
Location: ../test/lib/std/unit/infra/file_io_spec.spl
```

---

### 🔴 quality_spec

**File:** `home/ormastes/dev/pub/simple/test/build/quality_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.189591669+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `LintConfig` not found
Location: /home/ormastes/dev/pub/simple/test/build/quality_spec.spl
```

---

### 🔴 logger_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/logger_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.203743403+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/logger_spec.spl) [export_outside_init]
  --> line 4, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/logger_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/logger_spec.spl) [export_outside_init]
  --> line 6, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/logger_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/logger_spec.spl) [export_outside_init]
  --> line 10, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/logger_spec.spl) [export_outside_init]
  --> line 11, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/logger_spec.spl
```

---

### 🔴 regex_utils_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/regex_utils_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.215074825+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/regex_utils_spec.spl) [export_outside_init]
  --> line 256, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/regex_utils_spec.spl) [export_outside_init]
  --> line 257, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/regex_utils_spec.spl) [export_outside_init]
  --> line 258, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/regex_utils_spec.spl) [export_outside_init]
  --> line 259, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/regex_utils_spec.spl) [export_outside_init]
  --> line 260, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/regex_utils_spec.spl
```

---

### 🔴 resource_limits_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/concurrency/resource_limits_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.196802669+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/concurrency/resource_limits_spec.spl) [export_outside_init]
  --> line 316, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/concurrency/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/concurrency/resource_limits_spec.spl) [export_outside_init]
  --> line 317, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/concurrency/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/concurrency/resource_limits_spec.spl) [export_outside_init]
  --> line 318, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/concurrency/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/concurrency/resource_limits_spec.spl) [export_outside_init]
  --> line 319, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/concurrency/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/concurrency/resource_limits_spec.spl) [export_outside_init]
  --> line 320, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/concurrency/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/concurrency/resource_limits_spec.spl) [export_outside_init]
  --> line 321, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/concurrency/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/concurrency/resource_limits_spec.spl
```

---

### 🔴 component_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/game_engine/component_spec.spl`
**Category:** System
**Failed:** 2026-02-01T08:48:13.223896368+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/game_engine/component_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/game_engine/component_spec.spl) [export_outside_init]
  --> line 20, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/game_engine/component_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/game_engine/component_spec.spl) [export_outside_init]
  --> line 22, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/game_engine/component_spec.spl) [export_outside_init]
  --> line 23, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/game_engine/component_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/game_engine/component_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/game_engine/component_spec.spl) [export_outside_init]
  --> line 26, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/game_engine/component_spec.spl) [export_outside_init]
  --> line 27, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/game_engine/component_spec.spl) [export_outside_init]
  --> line 28, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/game_engine/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/system/features/game_engine/component_spec.spl
```

---

### 🔴 datetime_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/host/datetime_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.200699565+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/core/traits.spl": Unexpected token: expected identifier, found Into
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/host/datetime_spec.spl
```

---

### 🔴 compatibility_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/compatibility_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.208378157+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/compatibility_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/compatibility_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/compatibility_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/compatibility_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/compatibility_spec.spl
```

---

### 🔴 coverage_spec

**File:** `home/ormastes/dev/pub/simple/test/build/coverage_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.189448276+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `CoverageLevel` not found
Location: /home/ormastes/dev/pub/simple/test/build/coverage_spec.spl
```

---

### 🔴 bootstrap_spec

**File:** `home/ormastes/dev/pub/simple/test/build/bootstrap_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.189304261+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `BootstrapStage` not found
Location: /home/ormastes/dev/pub/simple/test/build/bootstrap_spec.spl
```

---

### 🔴 generic_template_spec

**File:** `test/lib/std/unit/compiler/generic_template_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.721220289+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Slash
Location: ../test/lib/std/unit/compiler/generic_template_spec.spl
```

---

### 🔴 linker_context_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/linker_context_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.196180632+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: function arguments: expected Comma, found Colon
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/linker_context_spec.spl
```

---

### 🔴 path_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/shell/path_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.209010353+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/path_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/path_spec.spl
```

---

### 🔴 traits_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/traits_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.218334495+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Indent
Location: /home/ormastes/dev/pub/simple/test/specs/traits_spec.spl
```

---

### 🔴 test_db_integrity_spec

**File:** `test/lib/std/unit/tooling/test_db_integrity_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.737890209+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: ../test/lib/std/unit/tooling/test_db_integrity_spec.spl
```

---

### 🔴 test_ffi_operator_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.206033833+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 123, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 124, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 125, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 126, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 127, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 128, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 129, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 330, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 331, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 332, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 333, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 334, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 335, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 336, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 337, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 338, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 339, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 340, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 341, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 342, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 343, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 344, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 345, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 346, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 347, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 348, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl
```

---

### 🔴 lexer_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/lexer_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.208518324+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Fn, found Identifier { name: "describe", pattern: Immutable }
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/lexer_spec.spl
```

---

### 🔴 sys_ffi_spec

**File:** `test/lib/std/unit/host/sys_ffi_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.725779919+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/host/common/io/term_types.spl": Unexpected token: expected Colon, found Newline
Location: ../test/lib/std/unit/host/sys_ffi_spec.spl
```

---

### 🔴 package_spec

**File:** `home/ormastes/dev/pub/simple/test/build/package_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.189519772+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `PackageType` not found
Location: /home/ormastes/dev/pub/simple/test/build/package_spec.spl
```

---

### 🔴 context_manager_spec

**File:** `test/lib/std/unit/core/context_manager_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.722755535+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/core/context_manager_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to ../test/lib/std/unit/core/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/core/context_manager_spec.spl) [export_outside_init]
  --> line 184, column 1
  = help: move this export to ../test/lib/std/unit/core/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/core/context_manager_spec.spl
```

---

### 🔴 traits_spec

**File:** `test/specs/traits_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.740424164+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Indent
Location: ../test/specs/traits_spec.spl
```

---

### 🔴 resource_limits_spec

**File:** `test/lib/std/unit/concurrency/resource_limits_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.722204592+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/concurrency/resource_limits_spec.spl) [export_outside_init]
  --> line 316, column 1
  = help: move this export to ../test/lib/std/unit/concurrency/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/concurrency/resource_limits_spec.spl) [export_outside_init]
  --> line 317, column 1
  = help: move this export to ../test/lib/std/unit/concurrency/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/concurrency/resource_limits_spec.spl) [export_outside_init]
  --> line 318, column 1
  = help: move this export to ../test/lib/std/unit/concurrency/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/concurrency/resource_limits_spec.spl) [export_outside_init]
  --> line 319, column 1
  = help: move this export to ../test/lib/std/unit/concurrency/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/concurrency/resource_limits_spec.spl) [export_outside_init]
  --> line 320, column 1
  = help: move this export to ../test/lib/std/unit/concurrency/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/concurrency/resource_limits_spec.spl) [export_outside_init]
  --> line 321, column 1
  = help: move this export to ../test/lib/std/unit/concurrency/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/concurrency/resource_limits_spec.spl
```

---

### 🔴 test_analysis_spec

**File:** `home/ormastes/dev/pub/simple/test/app/test_analysis_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.189151219+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: type mismatch: cannot convert dict to int
Location: /home/ormastes/dev/pub/simple/test/app/test_analysis_spec.spl
```

---

### 🔴 block_outline_info_spec

**File:** `home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.190644228+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 316, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 317, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 318, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 319, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 320, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 321, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 417, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 418, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 419, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 420, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 421, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 12, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 13, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 14, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 15, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 16, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 17, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 18, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 22, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 23, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 27, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 28, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 29, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 32, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 33, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 34, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 37, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 38, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 41, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 42, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 45, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 46, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 47, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 88, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 89, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 50, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 51, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 52, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 53, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 56, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 57, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 58, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 59, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 62, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 63, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 64, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 69, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 70, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 73, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 65, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 66, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 76, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 77, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 78, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 170, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 171, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 161, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 162, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 163, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 164, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 165, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 101, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 102, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 431, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 432, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 433, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 434, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 435, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 525, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 526, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 527, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 528, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 529, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 530, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 531, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 532, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 533, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 519, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 520, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 133, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 134, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 198, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 199, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 166, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 167, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 168, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 169, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 68, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 335, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 81, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 84, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
  --> line 85, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/compiler/blocks/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl
```

---

### 🔴 native_ffi_spec

**File:** `home/ormastes/dev/pub/simple/test/compiler/backend/native_ffi_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.190392347+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `slow_it` not found
Location: /home/ormastes/dev/pub/simple/test/compiler/backend/native_ffi_spec.spl
```

---

### 🔴 export_syntax_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/export_syntax_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.203465893+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/export_syntax_spec.spl) [export_outside_init]
  --> line 4, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/export_syntax_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/export_syntax_spec.spl) [export_outside_init]
  --> line 6, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/export_syntax_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/export_syntax_spec.spl) [export_outside_init]
  --> line 10, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/export_syntax_spec.spl) [export_outside_init]
  --> line 11, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/export_syntax_spec.spl
```

---

### 🔴 datetime_spec

**File:** `test/lib/std/unit/host/datetime_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.725717019+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/core/traits.spl": Unexpected token: expected identifier, found Into
Location: ../test/lib/std/unit/host/datetime_spec.spl
```

---

### 🔴 shell_api_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/shell_api_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.218138611+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Syntax error at 107:17: Cannot use 'exists' as a function name.

'exists' is a reserved keyword for existential quantifiers in verification:
Example: exists x in range: predicate

To check file/path existence, use 'exist' instead:
- file.exist(path)   # In shell module
- path.exist(path)   # In shell module
- file_exist(path)   # In infra module

Suggestion: Replace 'exists' with 'exist'
Location: /home/ormastes/dev/pub/simple/test/specs/shell_api_spec.spl
```

---

### 🔴 treesitter_tree_real_spec

**File:** `test/lib/std/unit/parser/treesitter_tree_real_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.732648414+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RBracket
Location: ../test/lib/std/unit/parser/treesitter_tree_real_spec.spl
```

---

### 🔴 progress_timing_test

**File:** `home/ormastes/dev/pub/simple/test/unit/spec/progress_timing_test.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.232178201+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/unit/spec/progress_timing_test.spl) [export_outside_init]
  --> line 101, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/unit/spec/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/unit/spec/progress_timing_test.spl) [export_outside_init]
  --> line 102, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/unit/spec/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/unit/spec/progress_timing_test.spl
```

---

### 🔴 treesitter_lexer_real_spec

**File:** `test/lib/std/unit/parser/treesitter_lexer_real_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.732268919+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RBracket
Location: ../test/lib/std/unit/parser/treesitter_lexer_real_spec.spl
```

---

### 🔴 bdd_timeout_minimal_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/system/spec/bdd_timeout_minimal_spec.spl`
**Category:** System
**Failed:** 2026-02-01T08:48:13.193639824+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/spec/bdd_timeout_minimal_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/spec/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/system/spec/bdd_timeout_minimal_spec.spl
```

---

### 🔴 treesitter_tokenkind_real_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_tokenkind_real_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.207563692+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RBracket
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_tokenkind_real_spec.spl
```

---

### 🔴 capability_effects_spec

**File:** `test/specs/capability_effects_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.739669171+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Colon
Location: ../test/specs/capability_effects_spec.spl
```

---

### 🔴 modules_spec

**File:** `test/specs/modules_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T07:57:01.740116035+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `test` not found
Location: ../test/specs/modules_spec.spl
```

---

### 🔴 differential_testing_spec

**File:** `home/ormastes/dev/pub/simple/test/compiler/backend/differential_testing_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T08:48:13.189911520+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Error("Invalid integer: 9223372036854775808")
Location: /home/ormastes/dev/pub/simple/test/compiler/backend/differential_testing_spec.spl
```

---

### 🔴 component_spec

**File:** `test/lib/std/unit/game_engine/component_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T07:57:01.724986051+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/game_engine/component_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to ../test/lib/std/unit/game_engine/__init__.spl (the directory manifest)

Location: ../test/lib/std/unit/game_engine/component_spec.spl
```

---

### 🔴 treesitter_tree_real_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_tree_real_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T08:48:13.207637433+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RBracket
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_tree_real_spec.spl
```

---

---

## 📊 Timing Analysis

---

## 🎯 Action Items

### Priority 1: Fix Failing Tests (251)

1. **metaprogramming_spec** - parse error: Unexpected token: expected expression, found Colon
2. **mock_simple_spec** - compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/lib/std/unit/spec/mock_simple_spec.spl) [export_outside_init]
3. **minimal_spec** - compile failed: lint: error: export statement not allowed in regular .spl files (found in ../test/system/features/database_synchronization/minimal_spec.spl) [export_outside_init]
4. **mock_direct_spec** - compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_direct_spec.spl) [export_outside_init]
5. **linker_context_spec** - parse error: function arguments: expected Comma, found Colon

