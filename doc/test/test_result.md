# Test Results

**Generated:** 2026-02-01 11:24:58
**Total Tests:** 1335
**Status:** ⚠️ 180 FAILED

## Summary

| Status | Count | Percentage |
|--------|-------|-----------|
| ✅ Passed | 1155 | 86.5% |
| ❌ Failed | 180 | 13.5% |
| ⏭️ Skipped | 0 | 0.0% |
| 🔕 Ignored | 0 | 0.0% |
| 🔐 Qualified Ignore | 0 | 0.0% |

---

## ❌ Failed Tests (180)

### 🔴 import_test

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/import_test.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.321467296+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/import_test.spl
```

---

### 🔴 tensor_bridge_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/features/math/tensor_bridge_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.334074527+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/math/tensor_bridge_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/math/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/system/features/math/tensor_bridge_spec.spl
```

---

### 🔴 fault_detection_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl`
**Category:** System
**Failed:** 2026-01-30T09:48:44.492008162+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `args` not found
Location: /home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl
```

---

### 🔴 block_outline_info_spec

**File:** `/home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.297826701+00:00
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

### 🔴 linker_context_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/linker_context_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.303330604+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: function arguments: expected Comma, found Colon
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/linker_context_spec.spl
```

---

### 🔴 arg_parsing_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/arg_parsing_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491636419+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/src/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/arg_parsing_spec.spl
```

---

### 🔴 decorators_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/core/decorators_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.304848092+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/core/decorators_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/core/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/core/decorators_spec.spl
```

---

### 🔴 class_method_call_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/interpreter/class_method_call_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.311093761+00:00
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

### 🔴 actor_model_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/actor_model_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.309446403+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/actor_model_spec.spl
```

---

### 🔴 compatibility_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/compatibility_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.318178553+00:00
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

### 🔴 roundtrip_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/roundtrip_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.318520500+00:00
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

### 🔴 type_inference_spec

**File:** `/home/ormastes/dev/pub/simple/test/specs/type_inference_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.326149008+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Newline
Location: /home/ormastes/dev/pub/simple/test/specs/type_inference_spec.spl
```

---

### 🔴 recurrent_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/recurrent_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.315605666+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/recurrent_spec.spl) [export_outside_init]
  --> line 3, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/recurrent_spec.spl) [export_outside_init]
  --> line 7, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/recurrent_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/recurrent_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/recurrent_spec.spl
```

---

### 🔴 stackless_coroutines_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/features/stackless_coroutines/stackless_coroutines_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.337381395+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found Dot
Location: /home/ormastes/dev/pub/simple/test/system/features/stackless_coroutines/stackless_coroutines_spec.spl
```

---

### 🔴 scene_node_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/features/game_engine/scene_node_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.332545196+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/game_engine/scene_node_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/game_engine/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/system/features/game_engine/scene_node_spec.spl
```

---

### 🔴 dataset_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/dataset_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.315252246+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/dataset_spec.spl) [export_outside_init]
  --> line 3, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/dataset_spec.spl) [export_outside_init]
  --> line 7, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/dataset_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/dataset_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/dataset_spec.spl
```

---

### 🔴 file_find_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/shell/file_find_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.318724272+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/file_find_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/file_find_spec.spl
```

---

### 🔴 transform_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/features/math/transform_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.334154811+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/math/transform_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/math/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/system/features/math/transform_spec.spl
```

---

### 🔴 import_test

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/import_test.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491787549+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/src/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/import_test.spl
```

---

### 🔴 bdd_timeout_minimal_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/system/spec/bdd_timeout_minimal_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.300811531+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/system/spec/bdd_timeout_minimal_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/system/spec/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/system/spec/bdd_timeout_minimal_spec.spl
```

---

### 🔴 parser_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/parser_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.318383697+00:00
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

### 🔴 block_definition_three_level_spec

**File:** `/home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.297741908+00:00
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

### 🔴 mcp_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/mcp_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.313833819+00:00
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

### 🔴 error_recovery_spec

**File:** `test/lib/std/unit/parser/error_recovery_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T10:20:08.832658003+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: function arguments: expected Comma, found Assign
Location: test/lib/std/unit/parser/error_recovery_spec.spl
```

---

### 🔴 tensor_interface_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/features/tensor_interface/tensor_interface_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.337790893+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/tensor_interface/tensor_interface_spec.spl) [export_outside_init]
  --> line 3, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/tensor_interface/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/tensor_interface/tensor_interface_spec.spl) [export_outside_init]
  --> line 7, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/tensor_interface/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/tensor_interface/tensor_interface_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/tensor_interface/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/tensor_interface/tensor_interface_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/tensor_interface/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/system/features/tensor_interface/tensor_interface_spec.spl
```

---

### 🔴 macro_spec

**File:** `/home/ormastes/dev/pub/simple/test/specs/macro_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.325487576+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `test` not found
Location: /home/ormastes/dev/pub/simple/test/specs/macro_spec.spl
```

---

### 🔴 logger_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/logger_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.313502833+00:00
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

### 🔴 test_ffi_operator_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/test_ffi_operator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.315815479+00:00
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

### 🔴 config_loader_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/features/config/config_loader_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.329769770+00:00
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

### 🔴 time_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/core/time_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.308564407+00:00
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

### 🔴 component_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/features/game_engine/component_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.332463379+00:00
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

### 🔴 mat4_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/features/math/mat4_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.333917264+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/math/mat4_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/math/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/system/features/math/mat4_spec.spl
```

---

### 🔴 regex_utils_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/regex_utils_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.322548395+00:00
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

### 🔴 process_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/shell/process_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.318868690+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/process_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/process_spec.spl
```

---

### 🔴 generic_template_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/generic_template_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.303122093+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Slash
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/generic_template_spec.spl
```

---

### 🔴 test_analysis_spec

**File:** `/home/ormastes/dev/pub/simple/test/app/test_analysis_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.296355773+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: type mismatch: cannot convert dict to int
Location: /home/ormastes/dev/pub/simple/test/app/test_analysis_spec.spl
```

---

### 🔴 exhaustiveness_validator_spec

**File:** `/home/ormastes/dev/pub/simple/test/compiler/backend/exhaustiveness_validator_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.297188695+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: function arguments: expected Comma, found Colon
Location: /home/ormastes/dev/pub/simple/test/compiler/backend/exhaustiveness_validator_spec.spl
```

---

### 🔴 lexer_spec

**File:** `test/lib/std/unit/sdn/lexer_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T10:19:54.506848795+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Fn, found Identifier { name: "describe", pattern: Immutable }
Location: test/lib/std/unit/sdn/lexer_spec.spl
```

---

### 🔴 mixin_comprehensive_test

**File:** `/home/ormastes/dev/pub/simple/test/integration/mixin_comprehensive_test.simple`
**Category:** Integration
**Failed:** 2026-02-01T11:24:58.298167837+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Colon, found Newline
Location: /home/ormastes/dev/pub/simple/test/integration/mixin_comprehensive_test.simple
```

---

### 🔴 minimal_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/features/database_synchronization/minimal_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.330569247+00:00
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

### 🔴 interpreter_bugs_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/system/bugs/interpreter_bugs_spec.spl`
**Category:** System
**Failed:** 2026-01-30T09:48:44.491095041+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `skip_it` not found
Location: /home/ormastes/dev/pub/simple/test/lib/std/system/bugs/interpreter_bugs_spec.spl
```

---

### 🔴 shapes_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491574019+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/src/lib/std/src/physics/collision/__init__.spl": Unexpected token: expected identifier, found LBrace
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl
```

---

### 🔴 test_db_validation_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/test_db_validation_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491840811+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/src/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/test_db_validation_spec.spl
```

---

### 🔴 treesitter_parser_real_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_parser_real_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491553059+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RBracket
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_parser_real_spec.spl
```

---

### 🔴 simple_math_integration_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/ml/simple_math_integration_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.315033145+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/simple_math_integration_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/simple_math_integration_spec.spl
```

---

### 🔴 spatial_hash_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491576314+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/src/lib/std/src/physics/collision/__init__.spl": Unexpected token: expected identifier, found LBrace
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl
```

---

### 🔴 server_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/lms/server_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491384095+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/src/lib/std/src/lms/sys.spl": Unexpected token: expected identifier, found LBrace
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/lms/server_spec.spl
```

---

### 🔴 memory_spec

**File:** `/home/ormastes/dev/pub/simple/test/specs/memory_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.325557591+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RParen
Location: /home/ormastes/dev/pub/simple/test/specs/memory_spec.spl
```

---

### 🔴 server_spec

**File:** `test/lib/std/unit/lms/server_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T10:20:30.765578923+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/src/lib/std/src/lms/sys.spl": Unexpected token: expected identifier, found LBrace
Location: test/lib/std/unit/lms/server_spec.spl
```

---

### 🔴 fault_detection_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/features/fault_detection/fault_detection_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.331632762+00:00
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

### 🔴 shell_api_spec

**File:** `/home/ormastes/dev/pub/simple/test/specs/shell_api_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.325842008+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `test` not found
Location: /home/ormastes/dev/pub/simple/test/specs/shell_api_spec.spl
```

---

### 🔴 suspension_operator_spec

**File:** `/home/ormastes/dev/pub/simple/test/specs/suspension_operator_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.325934746+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pointcut expression 'pc{...}', found LParen
Location: /home/ormastes/dev/pub/simple/test/specs/suspension_operator_spec.spl
```

---

### 🔴 spatial_hash_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/spatial_hash_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.317892102+00:00
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
  --> line 3, column 1
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

### 🔴 instruction_coverage_spec

**File:** `/home/ormastes/dev/pub/simple/test/compiler/backend/instruction_coverage_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.297269660+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Vec
Location: /home/ormastes/dev/pub/simple/test/compiler/backend/instruction_coverage_spec.spl
```

---

### 🔴 mixin_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/mixin_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.340240943+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found Pass
Location: /home/ormastes/dev/pub/simple/test/system/mixin_spec.spl
```

---

### 🔴 mock_direct_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_direct_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.319142136+00:00
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

### 🔴 traits_spec

**File:** `/home/ormastes/dev/pub/simple/test/specs/traits_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.326076318+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Indent
Location: /home/ormastes/dev/pub/simple/test/specs/traits_spec.spl
```

---

### 🔴 test_db_validation_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/test_db_validation_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.323301182+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/test_db_validation_spec.spl
```

---

### 🔴 datetime_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/host/datetime_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491364427+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/src/lib/std/src/host/common/io/error.spl": Unexpected token: expected Colon, found Newline
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/host/datetime_spec.spl
```

---

### 🔴 dependencies_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/dependencies_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.312951182+00:00
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

### 🔴 todo_parser_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/todo_parser_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.323572785+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/todo_parser_spec.spl
```

---

### 🔴 filter_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/diagram/filter_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.309306274+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/core/traits.spl": Unexpected token: expected identifier, found Into
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/diagram/filter_spec.spl
```

---

### 🔴 modules_spec

**File:** `/home/ormastes/dev/pub/simple/test/specs/modules_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.325700796+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `test` not found
Location: /home/ormastes/dev/pub/simple/test/specs/modules_spec.spl
```

---

### 🔴 treesitter_tokenkind_real_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_tokenkind_real_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491559672+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RBracket
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_tokenkind_real_spec.spl
```

---

### 🔴 mock_recorder_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_recorder_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.319213814+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_recorder_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_recorder_spec.spl
```

---

### 🔴 path_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/shell/path_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.318791582+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/path_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/path_spec.spl
```

---

### 🔴 treesitter_tokenkind_real_spec

**File:** `test/lib/std/unit/parser/treesitter_tokenkind_real_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T10:20:05.072410246+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RBracket
Location: test/lib/std/unit/parser/treesitter_tokenkind_real_spec.spl
```

---

### 🔴 actor_model_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/features/game_engine/actor_model_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.332382213+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 20, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 22, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 23, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 26, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 27, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 28, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/game_engine/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/system/features/game_engine/actor_model_spec.spl
```

---

### 🔴 async_default_spec

**File:** `/home/ormastes/dev/pub/simple/test/specs/async_default_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.325124789+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found On
Location: /home/ormastes/dev/pub/simple/test/specs/async_default_spec.spl
```

---

### 🔴 transformer_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/transformer_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.315895123+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/transformer_spec.spl) [export_outside_init]
  --> line 3, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/transformer_spec.spl) [export_outside_init]
  --> line 7, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/transformer_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/transformer_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/transformer_spec.spl
```

---

### 🔴 async_features_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/features/async_features/async_features_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.328475131+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found RParen
Location: /home/ormastes/dev/pub/simple/test/system/features/async_features/async_features_spec.spl
```

---

### 🔴 todo_parser_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/todo_tests/todo_parser_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491632331+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/src/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/todo_tests/todo_parser_spec.spl
```

---

### 🔴 file_io_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/system/sdn/file_io_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.300504009+00:00
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

### 🔴 document_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/document_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.318248447+00:00
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

### 🔴 treesitter_tree_real_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_tree_real_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491562177+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RBracket
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_tree_real_spec.spl
```

---

### 🔴 simple_math_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/simple_math_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.315676713+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/simple_math_spec.spl) [export_outside_init]
  --> line 3, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/simple_math_spec.spl) [export_outside_init]
  --> line 7, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/simple_math_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/simple_math_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/simple_math_spec.spl
```

---

### 🔴 treesitter_lexer_real_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_lexer_real_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.317021969+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RBracket
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_lexer_real_spec.spl
```

---

### 🔴 linalg_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/linalg_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.315462962+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/linalg_spec.spl) [export_outside_init]
  --> line 3, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/linalg_spec.spl) [export_outside_init]
  --> line 7, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/linalg_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/linalg_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/linalg_spec.spl
```

---

### 🔴 arg_parsing_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/arg_parsing_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.320034031+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/arg_parsing_spec.spl
```

---

### 🔴 lexer_ffi_test

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/compiler/lexer_ffi_test.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.298384664+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/core/traits.spl": Unexpected token: expected identifier, found Into
Location: /home/ormastes/dev/pub/simple/test/lib/std/compiler/lexer_ffi_test.spl
```

---

### 🔴 datetime_ffi_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/host/datetime_ffi_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.310403023+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/host/datetime_ffi_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/host/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/host/datetime_ffi_spec.spl
```

---

### 🔴 note_sdn_feature_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/features/compiler/note_sdn_feature_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-30T09:48:44.491084340+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `skip_it` not found
Location: /home/ormastes/dev/pub/simple/test/lib/std/features/compiler/note_sdn_feature_spec.spl
```

---

### 🔴 test_analysis_spec

**File:** `home/ormastes/dev/pub/simple/test/app/test_analysis_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-30T09:48:44.491074010+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: type mismatch: cannot convert dict to int
Location: /home/ormastes/dev/pub/simple/test/app/test_analysis_spec.spl
```

---

### 🔴 static_polymorphism_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/static_polymorphism_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.340388868+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Colon, found Identifier { name: "Item", pattern: TypeName }
Location: /home/ormastes/dev/pub/simple/test/system/static_polymorphism_spec.spl
```

---

### 🔴 static_method_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/codegen/static_method_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.302914113+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `feature` not found
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/codegen/static_method_spec.spl
```

---

### 🔴 types_spec

**File:** `/home/ormastes/dev/pub/simple/test/specs/types_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.326219173+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Let, found Struct
Location: /home/ormastes/dev/pub/simple/test/specs/types_spec.spl
```

---

### 🔴 autograd_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/autograd_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.315106817+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/autograd_spec.spl) [export_outside_init]
  --> line 3, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/autograd_spec.spl) [export_outside_init]
  --> line 7, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/autograd_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/autograd_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/autograd_spec.spl
```

---

### 🔴 treesitter_tree_real_spec

**File:** `test/lib/std/unit/parser/treesitter_tree_real_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T10:20:04.537545494+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RBracket
Location: test/lib/std/unit/parser/treesitter_tree_real_spec.spl
```

---

### 🔴 note_sdn_bdd_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/note_sdn_bdd_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491247403+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/simple/compiler/monomorphize/deferred.spl": Unexpected token: expected expression, found Slash
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/note_sdn_bdd_spec.spl
```

---

### 🔴 command_dispatch_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/command_dispatch_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491646919+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Dot
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/command_dispatch_spec.spl
```

---

### 🔴 aabb_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491565142+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/src/lib/std/src/physics/collision/__init__.spl": Unexpected token: expected identifier, found LBrace
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl
```

---

### 🔴 error_recovery_simple_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/parser/error_recovery_simple_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491521609+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `feature` not found
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/parser/error_recovery_simple_spec.spl
```

---

### 🔴 treesitter_lexer_real_spec

**File:** `test/lib/std/unit/parser/treesitter_lexer_real_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T10:20:04.004847751+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RBracket
Location: test/lib/std/unit/parser/treesitter_lexer_real_spec.spl
```

---

### 🔴 server_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/lms/server_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.311161100+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/core/traits.spl": Unexpected token: expected identifier, found Into
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/lms/server_spec.spl
```

---

### 🔴 file_io_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/infra/file_io_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491380007+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/src/lib/std/src/infra/alloc.spl": Unexpected token: expected Fn, found DocComment("Allocate memory of the given size.\nReturns a pointer (as i64) to the allocated memory.")
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/infra/file_io_spec.spl
```

---

### 🔴 basic_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/fs/basic_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.309374826+00:00
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

### 🔴 contact_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.317593278+00:00
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
  --> line 3, column 1
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

### 🔴 transport_edge_cases_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/transport_edge_cases_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.314604791+00:00
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

### 🔴 error_handler_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/error_handler_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.313157068+00:00
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

### 🔴 treesitter_parser_real_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_parser_real_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.317162730+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RBracket
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_parser_real_spec.spl
```

---

### 🔴 sys_ffi_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/host/sys_ffi_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.310542270+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/host/common/io/term_types.spl": Unexpected token: expected Fn, found Pass
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/host/sys_ffi_spec.spl
```

---

### 🔴 generic_template_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/generic_template_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491240680+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Slash
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/generic_template_spec.spl
```

---

### 🔴 activation_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/nn/activation_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.315534770+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/nn/activation_spec.spl) [export_outside_init]
  --> line 3, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/nn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/nn/activation_spec.spl) [export_outside_init]
  --> line 7, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/nn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/nn/activation_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/nn/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/nn/activation_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/nn/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/nn/activation_spec.spl
```

---

### 🔴 test_db_integrity_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/test_db_integrity_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.323229565+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/test_db_integrity_spec.spl
```

---

### 🔴 progress_timing_test

**File:** `/home/ormastes/dev/pub/simple/test/unit/spec/progress_timing_test.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.340798696+00:00
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

### 🔴 sys_ffi_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/host/sys_ffi_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491366611+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/src/lib/std/src/host/common/io/term_types.spl": Unexpected token: expected Colon, found Newline
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/host/sys_ffi_spec.spl
```

---

### 🔴 filter_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/diagram/filter_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491332095+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/src/lib/std/src/diagram/recorder.spl": Unexpected token: expected pattern, found Val
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/diagram/filter_spec.spl
```

---

### 🔴 metaprogramming_spec

**File:** `/home/ormastes/dev/pub/simple/test/specs/metaprogramming_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.325630752+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Colon
Location: /home/ormastes/dev/pub/simple/test/specs/metaprogramming_spec.spl
```

---

### 🔴 lexer_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/lexer_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.318316007+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Fn, found Identifier { name: "describe", pattern: Immutable }
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/lexer_spec.spl
```

---

### 🔴 value_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/value_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.318587309+00:00
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

### 🔴 capability_effects_spec

**File:** `/home/ormastes/dev/pub/simple/test/specs/capability_effects_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.325199823+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Colon
Location: /home/ormastes/dev/pub/simple/test/specs/capability_effects_spec.spl
```

---

### 🔴 differential_testing_spec

**File:** `/home/ormastes/dev/pub/simple/test/compiler/backend/differential_testing_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.297106727+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Error("Invalid integer: 9223372036854775808")
Location: /home/ormastes/dev/pub/simple/test/compiler/backend/differential_testing_spec.spl
```

---

### 🔴 command_dispatch_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/command_dispatch_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.320370958+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Dot
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/command_dispatch_spec.spl
```

---

### 🔴 env_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/shell/env_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.318654528+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/env_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/shell/env_spec.spl
```

---

### 🔴 file_io_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/infra/file_io_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.311020560+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/infra/concurrent.spl": Unexpected token: expected identifier, found DocComment("Create a new empty concurrent map.")
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/infra/file_io_spec.spl
```

---

### 🔴 datetime_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/host/datetime_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.310472947+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/core/traits.spl": Unexpected token: expected identifier, found Into
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/host/datetime_spec.spl
```

---

### 🔴 error_recovery_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/parser/error_recovery_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491524114+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: function arguments: expected Comma, found Assign
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/parser/error_recovery_spec.spl
```

---

### 🔴 rigidbody_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491582496+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/src/lib/std/src/physics/collision/__init__.spl": Unexpected token: expected identifier, found LBrace
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl
```

---

### 🔴 random_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/core/random_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.308226588+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/core/random_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/core/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/core/random_spec.spl
```

---

### 🔴 treesitter_tokenkind_real_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_tokenkind_real_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.317372182+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RBracket
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_tokenkind_real_spec.spl
```

---

### 🔴 feature_doc_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/system/feature_doc_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.298942016+00:00
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

### 🔴 note_sdn_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/note_sdn_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491249727+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/simple/compiler/monomorphize/deferred.spl": Unexpected token: expected expression, found Slash
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/note_sdn_spec.spl
```

---

### 🔴 linker_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/linker_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.303400178+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/core/traits.spl": Unexpected token: expected identifier, found Into
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/linker_spec.spl
```

---

### 🔴 vec3_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/features/math/vec3_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.334230076+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/math/vec3_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/math/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/system/features/math/vec3_spec.spl
```

---

### 🔴 test_db_integrity_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/test_db_integrity_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491838146+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/src/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/test_db_integrity_spec.spl
```

---

### 🔴 shapes_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/shapes_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.317808331+00:00
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
  --> line 3, column 1
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

### 🔴 file_io_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/system/sdn/file_io_spec.spl`
**Category:** System
**Failed:** 2026-01-30T09:48:44.491145628+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `skip_it` not found
Location: /home/ormastes/dev/pub/simple/test/lib/std/system/sdn/file_io_spec.spl
```

---

### 🔴 treesitter_lexer_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/features/treesitter/treesitter_lexer_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.338280945+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/treesitter/treesitter_lexer_spec.spl) [export_outside_init]
  --> line 342, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/treesitter/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/system/features/treesitter/treesitter_lexer_spec.spl
```

---

### 🔴 lexer_ffi_test

**File:** `home/ormastes/dev/pub/simple/test/lib/std/compiler/lexer_ffi_test.spl`
**Category:** Unknown
**Failed:** 2026-01-30T09:48:44.491081034+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `args` not found
Location: /home/ormastes/dev/pub/simple/test/lib/std/compiler/lexer_ffi_test.spl
```

---

### 🔴 error_recovery_simple_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/parser/error_recovery_simple_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.316105908+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `feature` not found
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/parser/error_recovery_simple_spec.spl
```

---

### 🔴 spec_matchers_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/system/spec/matchers/spec_matchers_spec.spl`
**Category:** System
**Failed:** 2026-01-30T09:48:44.491165596+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `skip_it` not found
Location: /home/ormastes/dev/pub/simple/test/lib/std/system/spec/matchers/spec_matchers_spec.spl
```

---

### 🔴 context_manager_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/core/context_manager_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.304566190+00:00
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

### 🔴 todo_parser_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/todo_parser_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491849317+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/src/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/todo_parser_spec.spl
```

---

### 🔴 export_syntax_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/export_syntax_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.313227804+00:00
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

### 🔴 pre_lex_per_dsl_spec

**File:** `/home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.298092683+00:00
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

### 🔴 concurrency_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/concurrency/concurrency_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.303672111+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found RParen
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/concurrency/concurrency_spec.spl
```

---

### 🔴 contact_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491567417+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/src/lib/std/src/physics/collision/__init__.spl": Unexpected token: expected identifier, found LBrace
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/contact_spec.spl
```

---

### 🔴 treesitter_lexer_real_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_lexer_real_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491548420+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RBracket
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_lexer_real_spec.spl
```

---

### 🔴 parser_error_recovery_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/features/parser/parser_error_recovery_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.335761781+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/parser/parser_error_recovery_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/parser/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/parser/parser_error_recovery_spec.spl) [export_outside_init]
  --> line 26, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/parser/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/system/features/parser/parser_error_recovery_spec.spl
```

---

### 🔴 backend_capability_spec

**File:** `/home/ormastes/dev/pub/simple/test/compiler/backend/backend_capability_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.297026413+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Vec
Location: /home/ormastes/dev/pub/simple/test/compiler/backend/backend_capability_spec.spl
```

---

### 🔴 component_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/component_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.309651057+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/component_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/component_spec.spl
```

---

### 🔴 todo_parser_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/todo_tests/todo_parser_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.319893861+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/todo_tests/todo_parser_spec.spl
```

---

### 🔴 error_recovery_simple_spec

**File:** `test/lib/std/unit/parser/error_recovery_simple_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T10:20:09.381762519+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `feature` not found
Location: test/lib/std/unit/parser/error_recovery_simple_spec.spl
```

---

### 🔴 treesitter_tree_real_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_tree_real_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.317445073+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RBracket
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/parser/treesitter_tree_real_spec.spl
```

---

### 🔴 db_sdn_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/db_sdn_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.327286665+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected fn, struct, class, enum, union, impl, mod, extern, or pub after attributes, found Identifier { name: "describe", pattern: Immutable }
Location: /home/ormastes/dev/pub/simple/test/system/db_sdn_spec.spl
```

---

### 🔴 regex_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/core/regex_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.308294168+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/core/regex_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/core/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/core/regex_spec.spl
```

---

### 🔴 bootstrap_spec

**File:** `/home/ormastes/dev/pub/simple/test/build/bootstrap_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.296504569+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `stage_name` not found
Location: /home/ormastes/dev/pub/simple/test/build/bootstrap_spec.spl
```

---

### 🔴 parser_improvements_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/system/improvements/parser_improvements_spec.spl`
**Category:** System
**Failed:** 2026-01-30T09:48:44.491102986+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `skip_it` not found
Location: /home/ormastes/dev/pub/simple/test/lib/std/system/improvements/parser_improvements_spec.spl
```

---

### 🔴 fft_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/fft_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.315392987+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/fft_spec.spl) [export_outside_init]
  --> line 3, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/fft_spec.spl) [export_outside_init]
  --> line 7, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/fft_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/fft_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/fft_spec.spl
```

---

### 🔴 synchronization_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/core/synchronization_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.308497288+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/core/synchronization_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/core/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/core/synchronization_spec.spl
```

---

### 🔴 quat_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/features/math/quat_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.333993902+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/math/quat_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/math/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/system/features/math/quat_spec.spl
```

---

### 🔴 pre_lex_info_spec

**File:** `/home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.298010054+00:00
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

### 🔴 aabb_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/aabb_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.317518905+00:00
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
  --> line 3, column 1
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

### 🔴 custom_autograd_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/custom_autograd_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.315180138+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/custom_autograd_spec.spl) [export_outside_init]
  --> line 3, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/custom_autograd_spec.spl) [export_outside_init]
  --> line 7, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/custom_autograd_spec.spl) [export_outside_init]
  --> line 8, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/custom_autograd_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/custom_autograd_spec.spl
```

---

### 🔴 block_skip_policy_spec

**File:** `/home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.297926904+00:00
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

### 🔴 concurrency_spec

**File:** `/home/ormastes/dev/pub/simple/test/specs/concurrency_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.325271661+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Case
Location: /home/ormastes/dev/pub/simple/test/specs/concurrency_spec.spl
```

---

### 🔴 syntax_spec

**File:** `/home/ormastes/dev/pub/simple/test/specs/syntax_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.326006043+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Indent
Location: /home/ormastes/dev/pub/simple/test/specs/syntax_spec.spl
```

---

### 🔴 dict_config_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/dict_config_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.315324315+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/dict_config_spec.spl) [export_outside_init]
  --> line 3, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/ml/torch/dict_config_spec.spl
```

---

### 🔴 resource_limits_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/concurrency/resource_limits_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.303962349+00:00
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

### 🔴 test_audio_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/test_audio_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.310068549+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/test_audio_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/game_engine/test_audio_spec.spl
```

---

### 🔴 failure_analysis_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/failure_analysis_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.313299762+00:00
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

### 🔴 functions_spec

**File:** `/home/ormastes/dev/pub/simple/test/specs/functions_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.325417452+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found LParen
Location: /home/ormastes/dev/pub/simple/test/specs/functions_spec.spl
```

---

### 🔴 error_recovery_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/parser/error_recovery_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.316177596+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: function arguments: expected Comma, found Assign
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/parser/error_recovery_spec.spl
```

---

### 🔴 context_pack_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/context_pack_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.320576033+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/core/traits.spl": Unexpected token: expected identifier, found Into
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/context_pack_spec.spl
```

---

### 🔴 vector_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/physics/core/vector_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.318031971+00:00
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

### 🔴 context_pack_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/context_pack_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491652951+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: Trait coherence errors:
OverlappingImpl { trait_name: "Add", type1: "text", type2: "text", span: Span { start: 2016, end: 2312, line: 76, column: 1 } }
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/tooling/context_pack_spec.spl
```

---

### 🔴 lexer_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/lexer_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T09:48:44.491588607+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Fn, found Identifier { name: "describe", pattern: Immutable }
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/lexer_spec.spl
```

---

### 🔴 treesitter_incremental_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/features/treesitter/treesitter_incremental_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.338198106+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/treesitter/treesitter_incremental_spec.spl) [export_outside_init]
  --> line 342, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/system/features/treesitter/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/system/features/treesitter/treesitter_incremental_spec.spl
```

---

### 🔴 test_meta_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/spec/test_meta_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.319615205+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/test_meta_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/test_meta_spec.spl
```

---

### 🔴 query_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/sdn/query_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.318451428+00:00
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

### 🔴 mock_simple_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_simple_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.319283808+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_simple_spec.spl) [export_outside_init]
  --> line 9, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/spec/mock_simple_spec.spl
```

---

### 🔴 treesitter_parser_real_spec

**File:** `test/lib/std/unit/parser/treesitter_parser_real_spec.spl`
**Category:** Unit
**Failed:** 2026-01-30T10:20:05.587736307+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RBracket
Location: test/lib/std/unit/parser/treesitter_parser_real_spec.spl
```

---

### 🔴 data_structures_spec

**File:** `/home/ormastes/dev/pub/simple/test/specs/data_structures_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.325344722+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Let, found Struct
Location: /home/ormastes/dev/pub/simple/test/specs/data_structures_spec.spl
```

---

### 🔴 jit_context_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/jit_context_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.303193761+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: function arguments: expected Comma, found Colon
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/jit_context_spec.spl
```

---

### 🔴 coverage_spec

**File:** `/home/ormastes/dev/pub/simple/test/build/coverage_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.296645120+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `coverage_level_to_string` not found
Location: /home/ormastes/dev/pub/simple/test/build/coverage_spec.spl
```

---

### 🔴 symbol_table_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/mcp/symbol_table_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.314532242+00:00
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

### 🔴 materials_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/materials_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.317733928+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/materials_spec.spl) [export_outside_init]
  --> line 5, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/collision/materials_spec.spl
```

---

### 🔴 test_integration_spec

**File:** `/home/ormastes/dev/pub/simple/test/build/test_integration_spec.spl`
**Category:** Integration
**Failed:** 2026-02-01T11:24:58.296857017+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `slow` not found
Location: /home/ormastes/dev/pub/simple/test/build/test_integration_spec.spl
```

---

### 🔴 rigidbody_spec

**File:** `/home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.318107446+00:00
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

error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl) [export_outside_init]
  --> line 3, column 1
  = help: move this export to /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/__init__.spl (the directory manifest)

Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/physics/dynamics/rigidbody_spec.spl
```

---

### 🔴 generic_bytecode_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/features/generic_bytecode_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-30T09:48:44.491087366+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `skip_it` not found
Location: /home/ormastes/dev/pub/simple/test/lib/std/features/generic_bytecode_spec.spl
```

---

---

## 📊 Timing Analysis

---

## 🎯 Action Items

### Priority 1: Fix Failing Tests (180)

1. **import_test** - compile failed: parse: in "/home/ormastes/dev/pub/simple/rust/lib/std/src/tooling/core/project.spl": Unexpected token: expected expression, found Newline
2. **tensor_bridge_spec** - compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/system/features/math/tensor_bridge_spec.spl) [export_outside_init]
3. **fault_detection_spec** - compile failed: semantic: function `args` not found
4. **block_outline_info_spec** - compile failed: lint: error: export statement not allowed in regular .spl files (found in /home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl) [export_outside_init]
5. **linker_context_spec** - parse error: function arguments: expected Comma, found Colon

### Priority 3: Stabilize Flaky Tests (6)

Tests with intermittent failures:
- fault_detection_spec (62.5% failure rate)
- string_helpers_spec (83.3% failure rate)
- parser_default_keyword_spec (12.5% failure rate)
- minimal_spec (42.9% failure rate)
- parser_skip_keyword_spec (41.7% failure rate)

