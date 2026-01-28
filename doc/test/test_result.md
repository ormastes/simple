# Test Results

**Generated:** 2026-01-28 12:27:01
**Total Tests:** 580
**Status:** ⚠️ 74 FAILED

## Summary

| Status | Count | Percentage |
|--------|-------|-----------|
| ✅ Passed | 506 | 87.2% |
| ❌ Failed | 74 | 12.8% |
| ⏭️ Skipped | 0 | 0.0% |
| 🔕 Ignored | 0 | 0.0% |
| 🔐 Qualified Ignore | 0 | 0.0% |

---

## ❌ Failed Tests (74)

### 🔴 lambda_block_spec

**File:** `tmp/lambda_block_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-27T11:46:22.338491268+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Comma, found Assign
Location: /tmp/lambda_block_spec.spl
```

---

### 🔴 parser_deprecation_warnings_spec

**File:** `test/system/features/parser/parser_deprecation_warnings_spec.spl`
**Category:** System
**Failed:** 2026-01-26T13:00:00.557834159+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Comma, found RawString("val s = \"This is List[T] in a string\"")
Location: test/system/features/parser/parser_deprecation_warnings_spec.spl
```

---

### 🔴 parser_keywords_spec

**File:** `tmp/parser_keywords_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-27T08:26:34.036415003+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Indent
Location: /tmp/parser_keywords_spec.spl
```

---

### 🔴 simple_math_spec

**File:** `test/lib/std/unit/ml/torch/simple_math_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T05:19:27.323056229+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected expression, found At
Location: test/lib/std/unit/ml/torch/simple_math_spec.spl
```

---

### 🔴 test_expect_array_spec

**File:** `tmp/test_expect_array_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-27T03:30:19.077777569+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected RBracket, found Comma
Location: /tmp/test_expect_array_spec.spl
```

---

### 🔴 parser_half_spec

**File:** `tmp/parser_half_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-27T07:12:30.147330744+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Assign
Location: /tmp/parser_half_spec.spl
```

---

### 🔴 autograd_spec

**File:** `test/lib/std/unit/ml/torch/autograd_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T05:49:41.966520009+00:00
**Flaky:** Yes (81.8% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected expression, found At
Location: test/lib/std/unit/ml/torch/autograd_spec.spl
```

---

### 🔴 di_spec

**File:** `simple/std_lib/test/unit/di_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T05:07:00.752631005+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Slash
Location: simple/std_lib/test/unit/di_spec.spl
```

---

### 🔴 spec_framework_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/system/spec/spec_framework_spec.spl`
**Category:** System
**Failed:** 2026-01-28T04:37:22.787186731+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test timed out after 30 seconds
Location: /home/ormastes/dev/pub/simple/test/lib/std/system/spec/spec_framework_spec.spl
```

---

### 🔴 tensor_spec

**File:** `simple/std_lib/test/features/tensor_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-28T05:11:56.475212419+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Comma
Location: simple/std_lib/test/features/tensor_spec.spl
```

---

### 🔴 bootstrap_spec

**File:** `simple/std_lib/test/features/bootstrap_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-28T05:12:39.357644596+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found And
Location: simple/std_lib/test/features/bootstrap_spec.spl
```

---

### 🔴 actor_model_spec

**File:** `test/lib/std/unit/game_engine/actor_model_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T05:28:05.850637906+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected Fn, found Var
Location: test/lib/std/unit/game_engine/actor_model_spec.spl
```

---

### 🔴 transformer_spec

**File:** `test/lib/std/unit/ml/torch/transformer_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T05:19:27.323073782+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected expression, found At
Location: test/lib/std/unit/ml/torch/transformer_spec.spl
```

---

### 🔴 linalg_spec

**File:** `test/lib/std/unit/ml/torch/linalg_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T05:19:27.323028225+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected expression, found At
Location: test/lib/std/unit/ml/torch/linalg_spec.spl
```

---

### 🔴 context_pack_spec

**File:** `test/lib/std/unit/tooling/context_pack_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T04:41:01.190498877+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected identifier, found Xor
Location: test/lib/std/unit/tooling/context_pack_spec.spl
```

---

### 🔴 min_test_spec

**File:** `tmp/min_test_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-27T11:16:10.717855320+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
failed to read /tmp/min_test_spec.spl: stream did not contain valid UTF-8
Location: /tmp/min_test_spec.spl
```

---

### 🔴 fuzz_spec

**File:** `src/lib/std/test/unit/testing/fuzz_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T05:11:40.868144598+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Val
Location: src/lib/std/test/unit/testing/fuzz_spec.spl
```

---

### 🔴 runner_spec

**File:** `test/lib/std/system/property/runner_spec.spl`
**Category:** System
**Failed:** 2026-01-28T04:58:22.112748893+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected identifier, found Xor
Location: test/lib/std/system/property/runner_spec.spl
```

---

### 🔴 input_spec

**File:** `test/lib/std/unit/game_engine/input_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T05:28:05.850776250+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected identifier, found Assign
Location: test/lib/std/unit/game_engine/input_spec.spl
```

---

### 🔴 test_exact_spec

**File:** `tmp/test_exact_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-27T07:40:22.086070538+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Fn, found Static
Location: /tmp/test_exact_spec.spl
```

---

### 🔴 treesitter_incremental_spec

**File:** `test/system/features/treesitter/treesitter_incremental_spec.spl`
**Category:** System
**Failed:** 2026-01-26T13:00:00.558217835+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found Newline
Location: test/system/features/treesitter/treesitter_incremental_spec.spl
```

---

### 🔴 ui_ssr_hydration_spec

**File:** `test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl`
**Category:** System
**Failed:** 2026-01-26T13:00:00.558324349+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Indent
Location: test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl
```

---

### 🔴 test_array3_spec

**File:** `tmp/test_array3_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-27T03:30:36.854120596+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected RBracket, found Comma
Location: /tmp/test_array3_spec.spl
```

---

### 🔴 fixture_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/fixtures/fixture_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-25T23:53:44.820840519+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test timed out after 30 seconds
Location: /home/ormastes/dev/pub/simple/test/lib/std/fixtures/fixture_spec.spl
```

---

### 🔴 generators_spec

**File:** `test/lib/std/system/property/generators_spec.spl`
**Category:** System
**Failed:** 2026-01-28T04:58:21.693991608+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected identifier, found Xor
Location: test/lib/std/system/property/generators_spec.spl
```

---

### 🔴 test_inject_spec

**File:** `tmp/test_inject_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-27T07:40:45.714845533+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Fn, found Static
Location: /tmp/test_inject_spec.spl
```

---

### 🔴 parser_175_spec

**File:** `tmp/parser_175_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-27T07:13:29.785432763+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected indented block after ':', found Dedent
Location: /tmp/parser_175_spec.spl
```

---

### 🔴 fft_spec

**File:** `test/lib/std/unit/ml/torch/fft_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T05:19:27.323018526+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected expression, found At
Location: test/lib/std/unit/ml/torch/fft_spec.spl
```

---

### 🔴 contact_spec

**File:** `test/lib/std/unit/physics/collision/contact_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T10:06:22.486004544+00:00
**Flaky:** No (95.1% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected identifier, found LBrace
Location: test/lib/std/unit/physics/collision/contact_spec.spl
```

---

### 🔴 feature_doc_spec

**File:** `test/lib/std/system/spec/feature_doc_spec.spl`
**Category:** System
**Failed:** 2026-01-28T05:03:42.039037794+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
compile failed: semantic: cannot modify self.features in immutable fn method
Location: test/lib/std/system/spec/feature_doc_spec.spl
```

---

### 🔴 generators_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/system/property/generators_spec.spl`
**Category:** System
**Failed:** 2026-01-28T04:36:02.125548785+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected identifier, found Xor
Location: /home/ormastes/dev/pub/simple/test/lib/std/system/property/generators_spec.spl
```

---

### 🔴 metrics_spec

**File:** `test/lib/std/unit/ml/engine/metrics_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T05:19:27.322922663+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected pattern, found Fn
Location: test/lib/std/unit/ml/engine/metrics_spec.spl
```

---

### 🔴 parser_type_annotations_spec

**File:** `test/system/features/parser/parser_type_annotations_spec.spl`
**Category:** System
**Failed:** 2026-01-26T13:00:00.557932617+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Vec
Location: test/system/features/parser/parser_type_annotations_spec.spl
```

---

### 🔴 promise_spec

**File:** `test/lib/std/unit/concurrency/promise_spec.spl`
**Category:** Unit
**Failed:** 2026-01-27T11:22:44.347993352+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Comma, found Identifier { name: "resolve", pattern: Immutable }
Location: test/lib/std/unit/concurrency/promise_spec.spl
```

---

### 🔴 table_spec

**File:** `simple/std_lib/test/features/table_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-28T05:12:27.922012401+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found Where
Location: simple/std_lib/test/features/table_spec.spl
```

---

### 🔴 ui_dynamic_structure_spec

**File:** `test/system/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl`
**Category:** System
**Failed:** 2026-01-26T13:00:00.558311945+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Indent
Location: test/system/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl
```

---

### 🔴 ui_structural_patchset_spec

**File:** `test/system/features/ui_structural_patchset/ui_structural_patchset_spec.spl`
**Category:** System
**Failed:** 2026-01-26T13:00:00.558338195+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Indent
Location: test/system/features/ui_structural_patchset/ui_structural_patchset_spec.spl
```

---

### 🔴 test_continuation_spec

**File:** `tmp/test_continuation_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-27T11:40:15.385475643+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Dedent
Location: /tmp/test_continuation_spec.spl
```

---

### 🔴 dataset_spec

**File:** `test/lib/std/unit/ml/torch/dataset_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T05:19:27.323009219+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected expression, found At
Location: test/lib/std/unit/ml/torch/dataset_spec.spl
```

---

### 🔴 contract_runtime_spec

**File:** `test/system/features/contracts/contract_runtime_spec.spl`
**Category:** System
**Failed:** 2026-01-26T13:00:00.556749899+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found From
Location: test/system/features/contracts/contract_runtime_spec.spl
```

---

### 🔴 contract_persistence_feature_spec

**File:** `src/lib/std/test/features/contract_persistence_feature_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-28T05:11:49.786515497+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Fn, found Colon
Location: src/lib/std/test/features/contract_persistence_feature_spec.spl
```

---

### 🔴 contract_runtime_spec

**File:** `tmp/contract_runtime_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-27T09:49:07.962655252+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found From
Location: /tmp/contract_runtime_spec.spl
```

---

### 🔴 hello_spec

**File:** `test/basic/hello_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-25T03:15:47.955872775+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
failed to read test/basic/hello_spec.spl: No such file or directory (os error 2)
Location: test/basic/hello_spec.spl
```

---

### 🔴 contact2_spec

**File:** `test/lib/std/unit/physics/collision/contact2_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T09:34:47.070916035+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
failed to read test/lib/std/unit/physics/collision/contact2_spec.spl: stream did not contain valid UTF-8
Location: test/lib/std/unit/physics/collision/contact2_spec.spl
```

---

### 🔴 test_comprehension_spec

**File:** `tmp/test_comprehension_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-26T09:57:53.104504678+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found For
Location: /tmp/test_comprehension_spec.spl
```

---

### 🔴 test_pub_static_spec

**File:** `tmp/test_pub_static_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-26T09:54:30.663629655+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found Static
Location: /tmp/test_pub_static_spec.spl
```

---

### 🔴 aop_around_advice_spec

**File:** `test/system/features/aop/aop_around_advice_spec.spl`
**Category:** System
**Failed:** 2026-01-27T01:23:53.106366618+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Indent
Location: test/system/features/aop/aop_around_advice_spec.spl
```

---

### 🔴 parser_196_spec

**File:** `tmp/parser_196_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-27T07:13:51.336831876+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Assign
Location: /tmp/parser_196_spec.spl
```

---

### 🔴 sdoctest_spec

**File:** `test/system/features/sdoctest/sdoctest_spec.spl`
**Category:** System
**Failed:** 2026-01-26T13:00:00.558044813+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected indented block after ':', found Error("Unexpected character: '`'")
Location: test/system/features/sdoctest/sdoctest_spec.spl
```

---

### 🔴 spatial_hash_spec

**File:** `test/lib/std/unit/physics/collision/spatial_hash_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T09:59:40.706932597+00:00
**Flaky:** No (93.5% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected Colon, found LBrace
Location: test/lib/std/unit/physics/collision/spatial_hash_spec.spl
```

---

### 🔴 test_expect_fn_spec

**File:** `tmp/test_expect_fn_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-27T03:32:09.061399486+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected RBracket, found Comma
Location: /tmp/test_expect_fn_spec.spl
```

---

### 🔴 sys_ffi_spec

**File:** `test/lib/std/unit/host/sys_ffi_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T04:38:07.030966721+00:00
**Flaky:** No (33.3% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected Fn, found Pub
Location: test/lib/std/unit/host/sys_ffi_spec.spl
```

---

### 🔴 recurrent_spec

**File:** `test/lib/std/unit/ml/torch/recurrent_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T05:19:27.323046811+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected expression, found At
Location: test/lib/std/unit/ml/torch/recurrent_spec.spl
```

---

### 🔴 material_spec

**File:** `test/lib/std/unit/game_engine/material_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T05:28:05.850786480+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected Fn, found Var
Location: test/lib/std/unit/game_engine/material_spec.spl
```

---

### 🔴 arg_parsing_spec

**File:** `test/lib/std/unit/tooling/arg_parsing_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T04:49:04.952440773+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: method `char_at` not found on type `array`
Location: test/lib/std/unit/tooling/arg_parsing_spec.spl
```

---

### 🔴 component_spec

**File:** `test/lib/std/unit/game_engine/component_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T05:28:05.850765720+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected identifier, found Assign
Location: test/lib/std/unit/game_engine/component_spec.spl
```

---

### 🔴 assets_spec

**File:** `test/lib/std/unit/game_engine/assets_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T05:28:05.850745291+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected identifier, found Assign
Location: test/lib/std/unit/game_engine/assets_spec.spl
```

---

### 🔴 config_env_spec

**File:** `test/lib/std/unit/infra/config_env_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T04:52:12.001151471+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected identifier, found Xor
Location: test/lib/std/unit/infra/config_env_spec.spl
```

---

### 🔴 trait_coherence_spec

**File:** `test/system/features/traits/trait_coherence_spec.spl`
**Category:** System
**Failed:** 2026-01-26T13:00:00.558170945+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Default
Location: test/system/features/traits/trait_coherence_spec.spl
```

---

### 🔴 config_spec

**File:** `simple/std_lib/test/unit/config_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T05:07:00.343285898+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Slash
Location: simple/std_lib/test/unit/config_spec.spl
```

---

### 🔴 parser_declarations_spec

**File:** `test/system/features/parser/parser_declarations_spec.spl`
**Category:** System
**Failed:** 2026-01-26T13:00:00.557821554+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Colon, found Newline
Location: test/system/features/parser/parser_declarations_spec.spl
```

---

### 🔴 server_spec

**File:** `test/lib/std/unit/lms/server_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T04:35:26.939359406+00:00
**Flaky:** No (33.3% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected identifier, found Fn
Location: test/lib/std/unit/lms/server_spec.spl
```

---

### 🔴 runner_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/system/property/runner_spec.spl`
**Category:** System
**Failed:** 2026-01-28T04:36:03.002473245+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected identifier, found Xor
Location: /home/ormastes/dev/pub/simple/test/lib/std/system/property/runner_spec.spl
```

---

### 🔴 note_sdn_spec

**File:** `test/lib/std/unit/compiler/note_sdn_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T12:25:34.543180618+00:00
**Flaky:** Yes (88.9% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected expression, found Newline
Location: test/lib/std/unit/compiler/note_sdn_spec.spl
```

---

### 🔴 shrinking_spec

**File:** `test/lib/std/system/property/shrinking_spec.spl`
**Category:** System
**Failed:** 2026-01-28T04:58:22.524244767+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected identifier, found Xor
Location: test/lib/std/system/property/shrinking_spec.spl
```

---

### 🔴 cli_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/unit/cli_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T04:38:49.456601770+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test timed out after 30 seconds
Location: /home/ormastes/dev/pub/simple/test/lib/std/unit/cli_spec.spl
```

---

### 🔴 dim_constraints_spec

**File:** `simple/compiler/test/dim_constraints_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-27T00:09:58.717980043+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found Literal
Location: simple/compiler/test/dim_constraints_spec.spl
```

---

### 🔴 custom_autograd_spec

**File:** `test/lib/std/unit/ml/torch/custom_autograd_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T05:19:27.322999861+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected expression, found At
Location: test/lib/std/unit/ml/torch/custom_autograd_spec.spl
```

---

### 🔴 force_fields_spec

**File:** `test/lib/std/unit/physics/dynamics/force_fields_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T09:50:57.391446227+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
failed to read test/lib/std/unit/physics/dynamics/force_fields_spec.spl: No such file or directory (os error 2)
Location: test/lib/std/unit/physics/dynamics/force_fields_spec.spl
```

---

### 🔴 set_spec

**File:** `test/lib/std/unit/core/set_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T06:00:29.220769228+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
failed to read test/lib/std/unit/core/set_spec.spl: No such file or directory (os error 2)
Location: test/lib/std/unit/core/set_spec.spl
```

---

### 🔴 file_io_spec

**File:** `test/lib/std/system/sdn/file_io_spec.spl`
**Category:** System
**Failed:** 2026-01-28T04:58:21.284234781+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected pattern, found Val
Location: test/lib/std/system/sdn/file_io_spec.spl
```

---

### 🔴 resource_cleanup_spec

**File:** `src/lib/std/test/features/resource_cleanup_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-28T05:24:14.342259969+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Fn, found Colon
Location: src/lib/std/test/features/resource_cleanup_spec.spl
```

---

### 🔴 treesitter_parser_spec

**File:** `test/system/features/treesitter/treesitter_parser_spec.spl`
**Category:** System
**Failed:** 2026-01-26T13:00:00.558241640+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Comma, found RawString("val d = {\"key\": \"value\"}")
Location: test/system/features/treesitter/treesitter_parser_spec.spl
```

---

### 🔴 activation_spec

**File:** `test/lib/std/unit/ml/torch/nn/activation_spec.spl`
**Category:** Unit
**Failed:** 2026-01-28T05:19:27.323037613+00:00
**Flaky:** No (50.0% failure rate)

**Error:**
```
compile failed: parse: Unexpected token: expected expression, found At
Location: test/lib/std/unit/ml/torch/nn/activation_spec.spl
```

---

---

## 📊 Timing Analysis

---

## 🎯 Action Items

### Priority 1: Fix Failing Tests (74)

1. **lambda_block_spec** - parse error: Unexpected token: expected Comma, found Assign
2. **parser_deprecation_warnings_spec** - parse error: Unexpected token: expected Comma, found RawString("val s = \"This is List[T] in a string\"")
3. **parser_keywords_spec** - parse error: Unexpected token: expected expression, found Indent
4. **simple_math_spec** - compile failed: parse: Unexpected token: expected expression, found At
5. **test_expect_array_spec** - parse error: Unexpected token: expected RBracket, found Comma

### Priority 3: Stabilize Flaky Tests (44)

Tests with intermittent failures:
- class_invariant_spec (33.3% failure rate)
- shared_pointers_spec (50.0% failure rate)
- autograd_spec (81.8% failure rate)
- parser_spec (66.7% failure rate)
- parser_expressions_spec (78.6% failure rate)

