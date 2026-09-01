# types_spec

> Purpose: Prove that Types.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# types_spec

Purpose: Prove that Types.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler_core/types_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Types.
Audience: COMP-CORE maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### Types

#### keeps core string span token and symbol helpers available

- Verify: keeps core string span token and symbol helpers available


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: keeps core string span token and symbol helpers available")
# @req: REQ-COMP-CORE-TYPES-001
val source = types_source()

assert_contains(source, "fn str_concat(a: text, b: text) -> text")
assert_contains(source, "fn str_len(s: text) -> i64:\n    rt_string_len(s)")
assert_contains(source, "fn str_contains(s: text, needle: text) -> bool")
assert_contains(source, "fn span_start(span_id: i64) -> i64")
assert_contains(source, "fn token_new(kind: i64, span_id: i64, value: text) -> i64")
assert_contains(source, "fn symbol_new(name: text, sym_type: i64, depth: i64, decl_id: i64, is_mut: i64) -> i64")
assert_contains(source, "fn scope_push() -> i64")
```

</details>

#### keeps type tags and type name conversion available

- Verify: keeps type tags and type name conversion available


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: keeps type tags and type name conversion available")
val source = types_source()

assert_contains(source, "val TYPE_VOID = 0")
assert_contains(source, "val TYPE_BOOL = 1")
assert_contains(source, "val TYPE_I64 = 2")
assert_contains(source, "val TYPE_OPTION = 14")
assert_contains(source, "val TYPE_RESULT = 19")
assert_contains(source, "val TYPE_FUTURE = 20")
assert_contains(source, "fn type_tag_name(tag: i64) -> text")
assert_contains(source, "fn type_tag_to_c(tag: i64) -> text")
```

</details>

#### keeps named type and function signature registries available

- Verify: keeps named type and function signature registries available


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: keeps named type and function signature registries available")
val source = types_source()

assert_contains(source, "fn named_type_register(name: text, field_names: [text], field_types: [i64]) -> i64")
assert_contains(source, "fn named_type_find(name: text) -> i64")
assert_contains(source, "fn named_type_field_type_tags(type_id: i64) -> [i64]")
assert_contains(source, "fn fn_sig_register(name: text, param_names: [text], param_types: [i64], ret_type: i64, is_ext: i64) -> i64")
assert_contains(source, "fn fn_sig_find(name: text) -> i64")
assert_contains(source, "fn reset_all_pools()")
```

</details>

#### keeps Dict and Result specialization ranges bounded and resettable

- Verify: keeps Dict and Result specialization ranges bounded and resettable


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: keeps Dict and Result specialization ranges bounded and resettable")
val source = types_source()

assert_contains(source, "val TYPE_DICT_BASE = 1000")
assert_contains(source, "val TYPE_RESULT_BASE = 2000")
assert_contains(source, "val TYPE_RESULT_LIMIT = 3000")
assert_contains(source, "val TYPE_NAMED_BASE = 10000")
assert_contains(source, "if idx >= TYPE_RESULT_BASE - TYPE_DICT_BASE:")
assert_contains(source, "if idx >= TYPE_RESULT_LIMIT - TYPE_RESULT_BASE:")
assert_contains(source, "result_type_ok = []")
assert_contains(source, "result_type_err = []")
assert_equal(source.contains("fn clear_i64_pool"), false)
```

</details>

#### interns and bounds every encoded composite type registry

- Verify: interns and bounds every encoded composite type registry


<details>
<summary>Executable SSpec</summary>

Runnable source: 97 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: interns and bounds every encoded composite type registry")
# Local raw tags keep this native-runnable through bootstrap compilers
# whose cross-module imported `val` representation is not yet stable.
val i64_tag = 2
val text_tag = 4
val any_tag = 12
val union_base = 500
val intersection_base = 600
val refinement_base = 700
val dict_base = 1000
val result_base = 2000
val tuple_base = 3000
val tuple_limit = 4000
val array_base = 4000
val array_limit = 5000
val named_base = 10000
reset_all_pools()
assert_equal(union_type_register([i64_tag, text_tag]), union_base)
assert_equal(union_type_register([i64_tag, text_tag]), union_base)
assert_equal(union_type_register([text_tag, i64_tag]), union_base + 1)
assert_equal(intersection_type_register([i64_tag, text_tag]), intersection_base)
assert_equal(intersection_type_register([i64_tag, text_tag]), intersection_base)
assert_equal(intersection_type_register([text_tag, i64_tag]), intersection_base + 1)
assert_equal(refinement_type_register(i64_tag, "value > 0"), refinement_base)
assert_equal(refinement_type_register(i64_tag, "value > 0"), refinement_base)
assert_equal(tuple_type_register([i64_tag, text_tag]), tuple_base)
assert_equal(tuple_type_register([i64_tag, text_tag]), tuple_base)
assert_equal(tuple_type_register([text_tag, i64_tag]), tuple_base + 1)
assert_equal(dict_type_register(i64_tag, text_tag), dict_base)
assert_equal(dict_type_register(i64_tag, text_tag), dict_base)
assert_equal(result_type_register(i64_tag, text_tag), result_base)
assert_equal(result_type_register(i64_tag, text_tag), result_base)
assert_equal(array_generic_type_register(named_base), array_base)
assert_equal(array_generic_type_register(named_base), array_base)
assert_equal(union_type_get_members(-1), [])
assert_equal(intersection_type_get_members(-1), [])
assert_equal(refinement_type_base(-1), any_tag)
assert_equal(refinement_type_predicate(-1), "")
assert_equal(tuple_type_get_elems(-1), [])
assert_equal(dict_type_get_key(-1), any_tag)
assert_equal(dict_type_get_value(-1), any_tag)
assert_equal(result_type_get_ok(-1), any_tag)
assert_equal(result_type_get_err(-1), any_tag)
assert_equal(array_generic_type_get_elem(-1), any_tag)

var union_last = union_base
for i in 2..(intersection_base - union_base):
    union_last = union_type_register([i64_tag, named_base + i])
assert_equal(union_last, intersection_base - 1)
assert_equal(union_type_register([i64_tag, text_tag]), union_base)
assert_equal(union_type_register([text_tag, -1]), -1)
var intersection_last = intersection_base
for i in 2..(refinement_base - intersection_base):
    intersection_last = intersection_type_register([i64_tag, named_base + i])
assert_equal(intersection_last, refinement_base - 1)
assert_equal(intersection_type_register([i64_tag, text_tag]), intersection_base)
assert_equal(intersection_type_register([text_tag, -1]), -1)
var refinement_last = refinement_base
for i in 1..(dict_base - refinement_base):
    refinement_last = refinement_type_register(i64_tag, "value > {i}")
assert_equal(refinement_last, dict_base - 1)
assert_equal(refinement_type_register(i64_tag, "value > 0"), refinement_base)
assert_equal(refinement_type_register(text_tag, "overflow"), -1)
var tuple_last = tuple_base
for i in 2..(tuple_limit - tuple_base):
    tuple_last = tuple_type_register([i64_tag, named_base + i])
assert_equal(tuple_last, tuple_limit - 1)
assert_equal(tuple_type_register([i64_tag, text_tag]), tuple_base)
assert_equal(tuple_type_register([text_tag, -1]), -1)
var dict_last = dict_base
for i in 1..(result_base - dict_base):
    dict_last = dict_type_register(named_base + i, text_tag)
assert_equal(dict_last, result_base - 1)
assert_equal(dict_type_register(i64_tag, text_tag), dict_base)
assert_equal(dict_type_register(-1, text_tag), -1)
var result_last = result_base
for i in 1..(tuple_base - result_base):
    result_last = result_type_register(named_base + i, text_tag)
assert_equal(result_last, tuple_base - 1)
assert_equal(result_type_register(i64_tag, text_tag), result_base)
assert_equal(result_type_register(-1, text_tag), -1)
var array_last = array_base
for i in 1..(array_limit - array_base):
    array_last = array_generic_type_register(named_base + i)
assert_equal(array_last, array_limit - 1)
assert_equal(array_generic_type_register(named_base), array_base)
assert_equal(array_generic_type_register(-1), -1)

reset_all_pools()
assert_equal(union_type_register([text_tag, i64_tag]), union_base)
assert_equal(intersection_type_register([text_tag, i64_tag]), intersection_base)
assert_equal(refinement_type_register(text_tag, "fresh"), refinement_base)
assert_equal(tuple_type_register([text_tag, i64_tag]), tuple_base)
assert_equal(dict_type_register(text_tag, i64_tag), dict_base)
assert_equal(result_type_register(text_tag, i64_tag), result_base)
assert_equal(array_generic_type_register(named_base + 1), array_base)
reset_all_pools()
```

</details>

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

- `REQ-COMP-CORE-TYPES-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a65426c1c778f68e7233b6775bc6296e434324c78641d99ad5fd3cfc270b58e6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a65426c1c778f68e7233b6775bc6296e434324c78641d99ad5fd3cfc270b58e6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a65426c1c778f68e7233b6775bc6296e434324c78641d99ad5fd3cfc270b58e6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/compiler_core/types_spec.spl
mirror: doc/06_spec/unit/compiler_core/types_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler_core/types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler_core/types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler_core/types_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/unit/compiler_core/types_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/unit/compiler_core/types_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps core string span token and symbol helpers available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/types_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps type tags and type name conversion available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/types_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps named type and function signature registries available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
