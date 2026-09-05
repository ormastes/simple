# Closed Discriminant Roundtrip Specification

> Tests covering closed enum discriminant roundtrip (S2 §10.1), roundtrip property, out-of-range decode fails closed, is_valid.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Closed Discriminant Roundtrip Specification

## Scenarios

### closed enum discriminant roundtrip (S2 §10.1)

### roundtrip property

#### decodes every declared discriminant back to its own variant

- decodes every declared discriminant back to its own variant
   - Expected: name equals `t.names[i]`
   - Expected: reencoded.unwrap() equals `raw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("decodes every declared discriminant back to its own variant")
# PROPERTY: for every declared value v, encode(decode(v)) == v.
val t = status_table()
var i = 0
while i < t.values.len():
    val raw = t.values[i]
    val decoded = t.decode(raw)
    assert_true(decoded.is_ok())
    val name = decoded.unwrap()
    expect(name).to_equal(t.names[i])
    val reencoded = t.encode(name)
    assert_true(reencoded.is_ok())
    expect(reencoded.unwrap()).to_equal(raw)
    i = i + 1
```

</details>

#### decodes every declared variant name back to its own discriminant

- decodes every declared variant name back to its own discriminant
   - Expected: enc.unwrap() equals `t.values[i]`
   - Expected: t.decode(enc.unwrap()).unwrap() equals `t.names[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("decodes every declared variant name back to its own discriminant")
val t = status_table()
var i = 0
while i < t.names.len():
    val enc = t.encode(t.names[i])
    assert_true(enc.is_ok())
    expect(enc.unwrap()).to_equal(t.values[i])
    expect(t.decode(enc.unwrap()).unwrap()).to_equal(t.names[i])
    i = i + 1
```

</details>

### out-of-range decode fails closed

#### fails on a value between two declared discriminants

- fails on a value between two declared discriminants
   - Expected: res.unwrap_err().raw equals `3`
   - Expected: res.unwrap_err().enum_name equals `Status`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails on a value between two declared discriminants")
val res = status_table().decode(3)
assert_true(res.is_err())
expect(res.unwrap_err().raw).to_equal(3)
expect(res.unwrap_err().enum_name).to_equal("Status")
```

</details>

#### fails on a value above every declared discriminant

- fails on a value above every declared discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails on a value above every declared discriminant")
assert_true(status_table().decode(256).is_err())
```

</details>

#### fails on a negative value rather than wrapping to variant zero

- fails on a negative value rather than wrapping to variant zero
   - Expected: res.unwrap_err().raw equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails on a negative value rather than wrapping to variant zero")
# NEIGHBOUR: the classic silent-fallback bug is decoding an
# invalid raw to the first variant. It must be an error.
val res = status_table().decode(-1)
assert_true(res.is_err())
expect(res.unwrap_err().raw).to_equal(-1)
```

</details>

#### fails on an undeclared variant name

- fails on an undeclared variant name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails on an undeclared variant name")
val res = status_table().encode("Nope")
assert_true(res.is_err())
```

</details>

#### reports the offending value in the error message

- reports the offending value in the error message


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports the offending value in the error message")
expect(status_table().decode(42).unwrap_err().message()).to_contain("42")
```

</details>

### is_valid

#### accepts a declared discriminant

- accepts a declared discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts a declared discriminant")
assert_true(status_table().is_valid(7))
```

</details>

#### rejects an undeclared discriminant

- rejects an undeclared discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects an undeclared discriminant")
assert_false(status_table().is_valid(8))
```

</details>

#### rejects every value on an empty table

- rejects every value on an empty table


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects every value on an empty table")
val empty = ClosedDiscriminantTable(enum_name: "Empty", names: [], values: [])
assert_false(empty.is_valid(0))
assert_true(empty.decode(0).is_err())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/enum_contract/closed_discriminant_roundtrip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering closed enum discriminant roundtrip (S2 §10.1), roundtrip property, out-of-range decode fails closed, is_valid.
- closed enum discriminant roundtrip (S2 §10.1)
- roundtrip property
- out-of-range decode fails closed
- is_valid

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `168ce5841f1f9d2fcb812289bf2bdbb0c54bbae3e76fdcf0c7e0bc7c88d074cb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `168ce5841f1f9d2fcb812289bf2bdbb0c54bbae3e76fdcf0c7e0bc7c88d074cb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `168ce5841f1f9d2fcb812289bf2bdbb0c54bbae3e76fdcf0c7e0bc7c88d074cb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/semantics/enum_contract/closed_discriminant_roundtrip_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/enum_contract/closed_discriminant_roundtrip_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantics/enum_contract/closed_discriminant_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/enum_contract/closed_discriminant_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/enum_contract/closed_discriminant_roundtrip_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/semantics/enum_contract/closed_discriminant_roundtrip_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes every declared discriminant back to its own variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/enum_contract/closed_discriminant_roundtrip_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes every declared variant name back to its own discriminant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/enum_contract/closed_discriminant_roundtrip_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails on a value between two declared discriminants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
