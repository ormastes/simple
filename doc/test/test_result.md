# Test Results

**Generated:** 2026-01-30 10:00:11
**Total Tests:** 691
**Status:** ⚠️ 37 FAILED

## Summary

| Status | Count | Percentage |
|--------|-------|-----------|
| ✅ Passed | 654 | 94.6% |
| ❌ Failed | 37 | 5.4% |
| ⏭️ Skipped | 0 | 0.0% |
| 🔕 Ignored | 0 | 0.0% |
| 🔐 Qualified Ignore | 0 | 0.0% |

---

## ❌ Failed Tests (37)

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

---

## 📊 Timing Analysis

---

## 🎯 Action Items

### Priority 1: Fix Failing Tests (37)

1. **lexer_ffi_test** - compile failed: semantic: function `args` not found
2. **fault_detection_spec** - compile failed: semantic: function `args` not found
3. **error_recovery_spec** - parse error: function arguments: expected Comma, found Assign
4. **test_analysis_spec** - compile failed: semantic: type mismatch: cannot convert dict to int
5. **generic_template_spec** - parse error: Unexpected token: expected expression, found Slash

### Priority 3: Stabilize Flaky Tests (6)

Tests with intermittent failures:
- parser_default_keyword_spec (14.3% failure rate)
- string_helpers_spec (83.3% failure rate)
- parser_static_keyword_spec (16.7% failure rate)
- minimal_spec (50.0% failure rate)
- parser_skip_keyword_spec (45.5% failure rate)

