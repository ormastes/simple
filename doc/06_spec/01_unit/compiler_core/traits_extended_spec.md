# Traits Extended Specification

> Tests covering Traits Extended.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Traits Extended Specification

## Scenarios

### Traits Extended

#### should expose method and combined member queries

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose method and combined member queries
   - Expected: src contains `if tr_query == "methods"`
   - Expected: src contains `val tr_mth_prefix = tr_mth_type_name + "__"`
   - Expected: src contains `if tr_query == "all_members"`
   - Expected: src contains `val tr_am_struct_decl = struct_table_lookup(tr_am_type_name)`
   - Expected: src contains `tr_am_result.push(val_make_text(tr_am_mname))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should expose method and combined member queries")
val src = traits_source()
expect(src.contains("if tr_query == \"methods\"")).to_equal(true)
expect(src.contains("val tr_mth_prefix = tr_mth_type_name + \"__\"")).to_equal(true)
expect(src.contains("if tr_query == \"all_members\"")).to_equal(true)
expect(src.contains("val tr_am_struct_decl = struct_table_lookup(tr_am_type_name)")).to_equal(true)
expect(src.contains("tr_am_result.push(val_make_text(tr_am_mname))")).to_equal(true)
```

</details>

#### should expose enum count class and function queries

- should expose enum count class and function queries
   - Expected: src contains `if tr_query == "enum_count"`
   - Expected: src contains `val tr_ec_variants_csv = enum_table_lookup(tr_ec_type_name)`
   - Expected: src contains `if tr_query == "is_class"`
   - Expected: src contains `if tr_query == "is_fn"`
   - Expected: src contains `val tr_if_decl = func_table_lookup(tr_if_name)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should expose enum count class and function queries")
val src = traits_source()
expect(src.contains("if tr_query == \"enum_count\"")).to_equal(true)
expect(src.contains("val tr_ec_variants_csv = enum_table_lookup(tr_ec_type_name)")).to_equal(true)
expect(src.contains("if tr_query == \"is_class\"")).to_equal(true)
expect(src.contains("if tr_query == \"is_fn\"")).to_equal(true)
expect(src.contains("val tr_if_decl = func_table_lookup(tr_if_name)")).to_equal(true)
```

</details>

#### should expose numeric kind queries

- should expose numeric kind queries
   - Expected: src contains `if tr_query == "is_integral"`
   - Expected: src contains `if tr_ii_name == "i64": return val_make_bool(true)`
   - Expected: src contains `if tr_query == "is_float"`
   - Expected: src contains `if tr_ifl_name == "f64": return val_make_bool(true)`
   - Expected: src contains `if tr_query == "is_numeric"`
   - Expected: src contains `if tr_in_name == "f32": return val_make_bool(true)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should expose numeric kind queries")
val src = traits_source()
expect(src.contains("if tr_query == \"is_integral\"")).to_equal(true)
expect(src.contains("if tr_ii_name == \"i64\": return val_make_bool(true)")).to_equal(true)
expect(src.contains("if tr_query == \"is_float\"")).to_equal(true)
expect(src.contains("if tr_ifl_name == \"f64\": return val_make_bool(true)")).to_equal(true)
expect(src.contains("if tr_query == \"is_numeric\"")).to_equal(true)
expect(src.contains("if tr_in_name == \"f32\": return val_make_bool(true)")).to_equal(true)
```

</details>

#### should expose container kind queries

- should expose container kind queries
   - Expected: src contains `if tr_query == "is_array"`
   - Expected: src contains `return val_make_bool(tr_ia_first == "[")`
   - Expected: src contains `if tr_query == "is_dict"`
   - Expected: src contains `return val_make_bool(tr_id_first == "{")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should expose container kind queries")
val src = traits_source()
expect(src.contains("if tr_query == \"is_array\"")).to_equal(true)
expect(src.contains("return val_make_bool(tr_ia_first == \"[\")")).to_equal(true)
expect(src.contains("if tr_query == \"is_dict\"")).to_equal(true)
expect(src.contains("return val_make_bool(tr_id_first == \"{\")")).to_equal(true)
```

</details>

#### should expose member type and set member queries

- should expose member type and set member queries
   - Expected: src contains `if tr_query == "member_type"`
   - Expected: src contains `val tr_mt_field_types = decl_get_field_types(tr_mt_struct_decl)`
   - Expected: src contains `return val_make_text(tr_mt_field_types[tr_mt_i])`
   - Expected: src contains `if tr_query == "set_member"`
   - Expected: src contains `val_struct_set_field(tr_sm_obj, tr_sm_field, tr_sm_new_val)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should expose member type and set member queries")
val src = traits_source()
expect(src.contains("if tr_query == \"member_type\"")).to_equal(true)
expect(src.contains("val tr_mt_field_types = decl_get_field_types(tr_mt_struct_decl)")).to_equal(true)
expect(src.contains("return val_make_text(tr_mt_field_types[tr_mt_i])")).to_equal(true)
expect(src.contains("if tr_query == \"set_member\"")).to_equal(true)
expect(src.contains("val_struct_set_field(tr_sm_obj, tr_sm_field, tr_sm_new_val)")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/traits_extended_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Traits Extended.
- Traits Extended

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER_CORE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `26ae944b181a1cb4cf87824179cab899d67ba86bbc74c98696e9f4aa0f2fbc5b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `26ae944b181a1cb4cf87824179cab899d67ba86bbc74c98696e9f4aa0f2fbc5b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `26ae944b181a1cb4cf87824179cab899d67ba86bbc74c98696e9f4aa0f2fbc5b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler_core/traits_extended_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/traits_extended_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/traits_extended_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/traits_extended_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/traits_extended_spec.spl:14:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose method and combined member queries' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/traits_extended_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose method and combined member queries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/traits_extended_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose enum count class and function queries' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/traits_extended_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose enum count class and function queries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/traits_extended_spec.spl:34:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose numeric kind queries' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/traits_extended_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose numeric kind queries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/traits_extended_spec.spl:45:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose container kind queries' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/traits_extended_spec.spl:54:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose member type and set member queries' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
