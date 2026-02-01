# Test Results

**Generated:** 2026-02-01 12:30:14
**Total Tests:** 854
**Status:** ⚠️ 94 FAILED

## Summary

| Status | Count | Percentage |
|--------|-------|-----------|
| ✅ Passed | 760 | 89.0% |
| ❌ Failed | 94 | 11.0% |
| ⏭️ Skipped | 0 | 0.0% |
| 🔕 Ignored | 0 | 0.0% |
| 🔐 Qualified Ignore | 0 | 0.0% |

---

## ❌ Failed Tests (94)

### 🔴 shell_api_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/shell_api_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.325842008+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `test` not found
Location: /home/ormastes/dev/pub/simple/test/specs/shell_api_spec.spl
```

---

### 🔴 mixin_comprehensive_test

**File:** `home/ormastes/dev/pub/simple/test/integration/mixin_comprehensive_test.simple`
**Category:** Integration
**Failed:** 2026-02-01T11:24:58.298167837+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Colon, found Newline
Location: /home/ormastes/dev/pub/simple/test/integration/mixin_comprehensive_test.simple
```

---

### 🔴 tensor_bridge_spec

**File:** `test/system/features/math/tensor_bridge_spec.spl`
**Category:** System
**Failed:** 2026-02-01T12:29:27.589192933+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in test/system/features/math/tensor_bridge_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to test/system/features/math/__init__.spl (the directory manifest)

Location: test/system/features/math/tensor_bridge_spec.spl
```

---

### 🔴 linker_context_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/linker_context_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.303330604+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: function arguments: expected Comma, found Colon
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/linker_context_spec.spl
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

### 🔴 db_sdn_spec

**File:** `home/ormastes/dev/pub/simple/test/system/db_sdn_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.327286665+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected fn, struct, class, enum, union, impl, mod, extern, or pub after attributes, found Identifier { name: "describe", pattern: Immutable }
Location: /home/ormastes/dev/pub/simple/test/system/db_sdn_spec.spl
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

### 🔴 memory_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/memory_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.325557591+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found RParen
Location: /home/ormastes/dev/pub/simple/test/specs/memory_spec.spl
```

---

### 🔴 bootstrap_spec

**File:** `home/ormastes/dev/pub/simple/test/build/bootstrap_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.296504569+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `stage_name` not found
Location: /home/ormastes/dev/pub/simple/test/build/bootstrap_spec.spl
```

---

### 🔴 actor_model_spec

**File:** `test/system/features/game_engine/actor_model_spec.spl`
**Category:** System
**Failed:** 2026-02-01T12:26:29.289627475+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in test/system/features/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in test/system/features/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 20, column 1
  = help: move this export to test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in test/system/features/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 21, column 1
  = help: move this export to test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in test/system/features/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 22, column 1
  = help: move this export to test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in test/system/features/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 23, column 1
  = help: move this export to test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in test/system/features/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 24, column 1
  = help: move this export to test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in test/system/features/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 25, column 1
  = help: move this export to test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in test/system/features/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 26, column 1
  = help: move this export to test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in test/system/features/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 27, column 1
  = help: move this export to test/system/features/game_engine/__init__.spl (the directory manifest)

error: export statement not allowed in regular .spl files (found in test/system/features/game_engine/actor_model_spec.spl) [export_outside_init]
  --> line 28, column 1
  = help: move this export to test/system/features/game_engine/__init__.spl (the directory manifest)

Location: test/system/features/game_engine/actor_model_spec.spl
```

---

### 🔴 vec3_spec

**File:** `test/system/features/math/vec3_spec.spl`
**Category:** System
**Failed:** 2026-02-01T12:29:27.589201108+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in test/system/features/math/vec3_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to test/system/features/math/__init__.spl (the directory manifest)

Location: test/system/features/math/vec3_spec.spl
```

---

### 🔴 exhaustiveness_validator_spec

**File:** `home/ormastes/dev/pub/simple/test/compiler/backend/exhaustiveness_validator_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.297188695+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: function arguments: expected Comma, found Colon
Location: /home/ormastes/dev/pub/simple/test/compiler/backend/exhaustiveness_validator_spec.spl
```

---

### 🔴 quat_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/math/quat_spec.spl`
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

### 🔴 vec3_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/math/vec3_spec.spl`
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

### 🔴 transform_spec

**File:** `test/system/features/math/transform_spec.spl`
**Category:** System
**Failed:** 2026-02-01T12:29:27.589197021+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in test/system/features/math/transform_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to test/system/features/math/__init__.spl (the directory manifest)

Location: test/system/features/math/transform_spec.spl
```

---

### 🔴 instruction_coverage_spec

**File:** `home/ormastes/dev/pub/simple/test/compiler/backend/instruction_coverage_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.297269660+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Vec
Location: /home/ormastes/dev/pub/simple/test/compiler/backend/instruction_coverage_spec.spl
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

### 🔴 backend_capability_spec

**File:** `home/ormastes/dev/pub/simple/test/compiler/backend/backend_capability_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.297026413+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Vec
Location: /home/ormastes/dev/pub/simple/test/compiler/backend/backend_capability_spec.spl
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

### 🔴 actor_model_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/game_engine/actor_model_spec.spl`
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

### 🔴 block_outline_info_spec

**File:** `home/ormastes/dev/pub/simple/test/compiler/blocks/block_outline_info_spec.spl`
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

### 🔴 transform_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/math/transform_spec.spl`
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

### 🔴 test_integration_spec

**File:** `home/ormastes/dev/pub/simple/test/build/test_integration_spec.spl`
**Category:** Integration
**Failed:** 2026-02-01T11:24:58.296857017+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `slow` not found
Location: /home/ormastes/dev/pub/simple/test/build/test_integration_spec.spl
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

### 🔴 concurrency_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/concurrency_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.325271661+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Case
Location: /home/ormastes/dev/pub/simple/test/specs/concurrency_spec.spl
```

---

### 🔴 coverage_spec

**File:** `home/ormastes/dev/pub/simple/test/build/coverage_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.296645120+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `coverage_level_to_string` not found
Location: /home/ormastes/dev/pub/simple/test/build/coverage_spec.spl
```

---

### 🔴 syntax_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/syntax_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.326006043+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Indent
Location: /home/ormastes/dev/pub/simple/test/specs/syntax_spec.spl
```

---

### 🔴 type_inference_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/type_inference_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.326149008+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Newline
Location: /home/ormastes/dev/pub/simple/test/specs/type_inference_spec.spl
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

### 🔴 quat_spec

**File:** `test/system/features/math/quat_spec.spl`
**Category:** System
**Failed:** 2026-02-01T12:29:27.589188615+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in test/system/features/math/quat_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to test/system/features/math/__init__.spl (the directory manifest)

Location: test/system/features/math/quat_spec.spl
```

---

### 🔴 tensor_bridge_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/math/tensor_bridge_spec.spl`
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

### 🔴 jit_context_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/jit_context_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.303193761+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: function arguments: expected Comma, found Colon
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/compiler/jit_context_spec.spl
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

### 🔴 data_structures_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/data_structures_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.325344722+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Let, found Struct
Location: /home/ormastes/dev/pub/simple/test/specs/data_structures_spec.spl
```

---

### 🔴 functions_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/functions_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.325417452+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found LParen
Location: /home/ormastes/dev/pub/simple/test/specs/functions_spec.spl
```

---

### 🔴 differential_testing_spec

**File:** `home/ormastes/dev/pub/simple/test/compiler/backend/differential_testing_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.297106727+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Error("Invalid integer: 9223372036854775808")
Location: /home/ormastes/dev/pub/simple/test/compiler/backend/differential_testing_spec.spl
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

### 🔴 metaprogramming_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/metaprogramming_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.325630752+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Colon
Location: /home/ormastes/dev/pub/simple/test/specs/metaprogramming_spec.spl
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

### 🔴 suspension_operator_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/suspension_operator_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.325934746+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pointcut expression 'pc{...}', found LParen
Location: /home/ormastes/dev/pub/simple/test/specs/suspension_operator_spec.spl
```

---

### 🔴 block_definition_three_level_spec

**File:** `home/ormastes/dev/pub/simple/test/compiler/blocks/block_definition_three_level_spec.spl`
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

### 🔴 mat4_spec

**File:** `test/system/features/math/mat4_spec.spl`
**Category:** System
**Failed:** 2026-02-01T12:29:27.589183204+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: lint: error: export statement not allowed in regular .spl files (found in test/system/features/math/mat4_spec.spl) [export_outside_init]
  --> line 39, column 1
  = help: move this export to test/system/features/math/__init__.spl (the directory manifest)

Location: test/system/features/math/mat4_spec.spl
```

---

### 🔴 traits_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/traits_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.326076318+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Indent
Location: /home/ormastes/dev/pub/simple/test/specs/traits_spec.spl
```

---

### 🔴 comment_only_spec

**File:** `test/meta/comment_only_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:56:24.981364518+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
failed to read test/meta/comment_only_spec.spl: No such file or directory (os error 2)
Location: test/meta/comment_only_spec.spl
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

### 🔴 static_method_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/codegen/static_method_spec.spl`
**Category:** Unit
**Failed:** 2026-02-01T11:24:58.302914113+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `feature` not found
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/codegen/static_method_spec.spl
```

---

### 🔴 mat4_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/math/mat4_spec.spl`
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

### 🔴 async_default_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/async_default_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.325124789+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found On
Location: /home/ormastes/dev/pub/simple/test/specs/async_default_spec.spl
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

### 🔴 modules_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/modules_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.325700796+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `test` not found
Location: /home/ormastes/dev/pub/simple/test/specs/modules_spec.spl
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

### 🔴 scene_node_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/game_engine/scene_node_spec.spl`
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

### 🔴 types_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/types_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.326219173+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Let, found Struct
Location: /home/ormastes/dev/pub/simple/test/specs/types_spec.spl
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

### 🔴 mixin_spec

**File:** `home/ormastes/dev/pub/simple/test/system/mixin_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.340240943+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found Pass
Location: /home/ormastes/dev/pub/simple/test/system/mixin_spec.spl
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

### 🔴 block_skip_policy_spec

**File:** `home/ormastes/dev/pub/simple/test/compiler/blocks/block_skip_policy_spec.spl`
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

### 🔴 macro_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/macro_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.325487576+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `test` not found
Location: /home/ormastes/dev/pub/simple/test/specs/macro_spec.spl
```

---

### 🔴 pre_lex_info_spec

**File:** `home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_info_spec.spl`
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

### 🔴 component_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/game_engine/component_spec.spl`
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

### 🔴 static_polymorphism_spec

**File:** `home/ormastes/dev/pub/simple/test/system/static_polymorphism_spec.spl`
**Category:** System
**Failed:** 2026-02-01T11:24:58.340388868+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Colon, found Identifier { name: "Item", pattern: TypeName }
Location: /home/ormastes/dev/pub/simple/test/system/static_polymorphism_spec.spl
```

---

### 🔴 pre_lex_per_dsl_spec

**File:** `home/ormastes/dev/pub/simple/test/compiler/blocks/pre_lex_per_dsl_spec.spl`
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

### 🔴 capability_effects_spec

**File:** `home/ormastes/dev/pub/simple/test/specs/capability_effects_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-01T11:24:58.325199823+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Colon
Location: /home/ormastes/dev/pub/simple/test/specs/capability_effects_spec.spl
```

---

---

## 📊 Timing Analysis

---

## 🎯 Action Items

### Priority 1: Fix Failing Tests (94)

1. **shell_api_spec** - compile failed: semantic: function `test` not found
2. **mixin_comprehensive_test** - parse error: Unexpected token: expected Colon, found Newline
3. **tensor_bridge_spec** - compile failed: lint: error: export statement not allowed in regular .spl files (found in test/system/features/math/tensor_bridge_spec.spl) [export_outside_init]
4. **linker_context_spec** - parse error: function arguments: expected Comma, found Colon
5. **treesitter_parser_real_spec** - parse error: Unexpected token: expected expression, found RBracket

### Priority 3: Stabilize Flaky Tests (6)

Tests with intermittent failures:
- parser_static_keyword_spec (14.3% failure rate)
- string_helpers_spec (83.3% failure rate)
- parser_skip_keyword_spec (41.7% failure rate)
- fault_detection_spec (62.5% failure rate)
- parser_default_keyword_spec (12.5% failure rate)

