# Enum Payload Capture Specification

> Tests covering enum variant payload types are captured, not discarded, at parse time.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enum Payload Capture Specification

## Scenarios

### enum variant payload types are captured, not discarded, at parse time

#### captures a single-field payload variant (Some(payload: i64)) with the right type

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- captures a single-field payload variant (Some(payload: i64)) with the right type


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures a single-field payload variant (Some(payload: i64)) with the right type")
val src = "enum E:\n" +
    "    Some(payload: i64)\n" +
    "    None\n" +
    "\n" +
    "fn identity(n: i64) -> i64:\n" +
    "    n\n"
val parsed = parse_full_frontend(src, "testdata/fixture_epc1_some.spl", "fixture_epc1_some", Logger(level: 0))
assert_false(parser_has_errors())
assert_true(parsed.enums.contains_key("E"))
val e = parsed.enums["E"]
val some_idx = find_variant_index(e.variants, "Some")
assert_true(some_idx >= 0)
val some_types = variant_tuple_type_names(e.variants[some_idx])
assert_equal(some_types.len(), 1)
assert_equal(some_types[0], "i64")
```

</details>

#### leaves payload-less variants with an empty Tuple([]) kind

- leaves payload-less variants with an empty Tuple([]) kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves payload-less variants with an empty Tuple([]) kind")
val src = "enum E:\n" +
    "    Some(payload: i64)\n" +
    "    None\n" +
    "\n" +
    "fn identity(n: i64) -> i64:\n" +
    "    n\n"
val parsed = parse_full_frontend(src, "testdata/fixture_epc1_none.spl", "fixture_epc1_none", Logger(level: 0))
assert_false(parser_has_errors())
assert_true(parsed.enums.contains_key("E"))
val e = parsed.enums["E"]
val none_idx = find_variant_index(e.variants, "None")
assert_true(none_idx >= 0)
val none_types = variant_tuple_type_names(e.variants[none_idx])
assert_equal(none_types.len(), 0)
```

</details>

#### captures a mixed enum (payload variants and plain variants) correctly per-variant

- captures a mixed enum (payload variants and plain variants) correctly per-variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures a mixed enum (payload variants and plain variants) correctly per-variant")
val src = "enum Status:\n" +
    "    Ok(value: i64)\n" +
    "    Err(msg: text)\n" +
    "    Pending\n" +
    "\n" +
    "fn make() -> i64:\n" +
    "    1\n"
val parsed = parse_full_frontend(src, "testdata/fixture_epc1_mixed.spl", "fixture_epc1_mixed", Logger(level: 0))
assert_false(parser_has_errors())
assert_true(parsed.enums.contains_key("Status"))
val e = parsed.enums["Status"]
val ok_idx = find_variant_index(e.variants, "Ok")
val err_idx = find_variant_index(e.variants, "Err")
val pending_idx = find_variant_index(e.variants, "Pending")
assert_true(ok_idx >= 0)
assert_true(err_idx >= 0)
assert_true(pending_idx >= 0)
val ok_types = variant_tuple_type_names(e.variants[ok_idx])
val err_types = variant_tuple_type_names(e.variants[err_idx])
val pending_types = variant_tuple_type_names(e.variants[pending_idx])
assert_equal(ok_types.len(), 1)
assert_equal(ok_types[0], "i64")
assert_equal(err_types.len(), 1)
assert_equal(err_types[0], "text")
assert_equal(pending_types.len(), 0)
```

</details>

#### EPA1: captures BOTH fields of a two-field payload variant (Pair(a: i64, b: text)), in order

- EPA1: captures BOTH fields of a two-field payload variant (Pair(a: i64, b: text)), in order


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EPA1: captures BOTH fields of a two-field payload variant (Pair(a: i64, b: text)), in order")
val src = "enum Pair:\n" +
    "    Both(a: i64, b: text)\n" +
    "\n" +
    "fn make() -> i64:\n" +
    "    1\n"
val parsed = parse_full_frontend(src, "testdata/fixture_epa1_pair.spl", "fixture_epa1_pair", Logger(level: 0))
assert_false(parser_has_errors())
assert_true(parsed.enums.contains_key("Pair"))
val e = parsed.enums["Pair"]
val both_idx = find_variant_index(e.variants, "Both")
assert_true(both_idx >= 0)
val both_types = variant_tuple_type_names(e.variants[both_idx])
assert_equal(both_types.len(), 2)
assert_equal(both_types[0], "i64")
assert_equal(both_types[1], "text")
```

</details>

#### EPA1: captures all three fields of a three-field payload variant, in order

- EPA1: captures all three fields of a three-field payload variant, in order


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EPA1: captures all three fields of a three-field payload variant, in order")
val src = "enum Triple:\n" +
    "    All(a: i64, b: text, c: bool)\n" +
    "\n" +
    "fn make() -> i64:\n" +
    "    1\n"
val parsed = parse_full_frontend(src, "testdata/fixture_epa1_triple.spl", "fixture_epa1_triple", Logger(level: 0))
assert_false(parser_has_errors())
assert_true(parsed.enums.contains_key("Triple"))
val e = parsed.enums["Triple"]
val all_idx = find_variant_index(e.variants, "All")
assert_true(all_idx >= 0)
val all_types = variant_tuple_type_names(e.variants[all_idx])
assert_equal(all_types.len(), 3)
assert_equal(all_types[0], "i64")
assert_equal(all_types[1], "text")
assert_equal(all_types[2], "bool")
```

</details>

#### EPA1: a mixed enum with varying arities keeps each variant's own field count and types straight

- EPA1: a mixed enum with varying arities keeps each variant's own field count and types straight


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EPA1: a mixed enum with varying arities keeps each variant's own field count and types straight")
val src = "enum Mixed:\n" +
    "    Zero\n" +
    "    One(x: i64)\n" +
    "    Two(x: i64, y: text)\n" +
    "    Three(x: i64, y: text, z: bool)\n" +
    "\n" +
    "fn make() -> i64:\n" +
    "    1\n"
val parsed = parse_full_frontend(src, "testdata/fixture_epa1_mixed_arity.spl", "fixture_epa1_mixed_arity", Logger(level: 0))
assert_false(parser_has_errors())
assert_true(parsed.enums.contains_key("Mixed"))
val e = parsed.enums["Mixed"]
val zero_idx = find_variant_index(e.variants, "Zero")
val one_idx = find_variant_index(e.variants, "One")
val two_idx = find_variant_index(e.variants, "Two")
val three_idx = find_variant_index(e.variants, "Three")
assert_true(zero_idx >= 0)
assert_true(one_idx >= 0)
assert_true(two_idx >= 0)
assert_true(three_idx >= 0)
val zero_types = variant_tuple_type_names(e.variants[zero_idx])
val one_types = variant_tuple_type_names(e.variants[one_idx])
val two_types = variant_tuple_type_names(e.variants[two_idx])
val three_types = variant_tuple_type_names(e.variants[three_idx])
assert_equal(zero_types.len(), 0)
assert_equal(one_types.len(), 1)
assert_equal(one_types[0], "i64")
assert_equal(two_types.len(), 2)
assert_equal(two_types[0], "i64")
assert_equal(two_types[1], "text")
assert_equal(three_types.len(), 3)
assert_equal(three_types[0], "i64")
assert_equal(three_types[1], "text")
assert_equal(three_types[2], "bool")
```

</details>

#### leaves a fully payload-less enum with every variant at Tuple([])

- leaves a fully payload-less enum with every variant at Tuple([])


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves a fully payload-less enum with every variant at Tuple([])")
val src = "enum Color:\n" +
    "    Red\n" +
    "    Green\n" +
    "    Blue\n" +
    "\n" +
    "fn make() -> i64:\n" +
    "    1\n"
val parsed = parse_full_frontend(src, "testdata/fixture_epc1_clean.spl", "fixture_epc1_clean", Logger(level: 0))
assert_false(parser_has_errors())
assert_true(parsed.enums.contains_key("Color"))
val e = parsed.enums["Color"]
assert_equal(e.variants.len(), 3)
for v in e.variants:
    assert_equal(variant_tuple_type_names(v).len(), 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/enum_payload_capture_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering enum variant payload types are captured, not discarded, at parse time.
- enum variant payload types are captured, not discarded, at parse time

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c435123052502e8e71577b0eb0f3eb385213405d18fb95bf0b29a06e33038f01`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c435123052502e8e71577b0eb0f3eb385213405d18fb95bf0b29a06e33038f01`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c435123052502e8e71577b0eb0f3eb385213405d18fb95bf0b29a06e33038f01`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/frontend/enum_payload_capture_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/enum_payload_capture_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/enum_payload_capture_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/enum_payload_capture_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/enum_payload_capture_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'captures a single-field payload variant (Some(payload: i64)) with the right type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/enum_payload_capture_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves payload-less variants with an empty Tuple([]) kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/enum_payload_capture_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'captures a mixed enum (payload variants and plain variants) correctly per-variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
