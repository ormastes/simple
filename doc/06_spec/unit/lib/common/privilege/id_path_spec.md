# IdPath Specification

> Exercises `IdPath` intern table, prefix match, subdivide, and segment validation

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# IdPath Specification

Exercises `IdPath` intern table, prefix match, subdivide, and segment validation

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Red (no impl yet) |
| Source | `test/unit/lib/common/privilege/id_path_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises `IdPath` intern table, prefix match, subdivide, and segment validation
defined in Phase 3 architecture (`src/lib/common/privilege/id_path.spl`).

## Scenarios

### IdPath

### intern

#### AC-1: returns identical intern_id for identical strings

- AC-1: returns identical intern_id for identical strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: returns identical intern_id for identical strings")
val a = id_path_intern("id.user.banking")
val b = id_path_intern("id.user.banking")
expect a.intern_id to_equal b.intern_id
```

</details>

#### AC-1: returns distinct intern_id for distinct strings

- AC-1: returns distinct intern_id for distinct strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: returns distinct intern_id for distinct strings")
val a = id_path_intern("id.user.banking")
val b = id_path_intern("id.user.mail")
val equal = (a.intern_id == b.intern_id)
expect equal to_equal false
```

</details>

#### AC-1: splits dotted path into ordered segments

- AC-1: splits dotted path into ordered segments


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: splits dotted path into ordered segments")
val p = id_path_intern("id.user.banking")
expect p.segments to_contain "id"
expect p.segments to_contain "user"
expect p.segments to_contain "banking"
```

</details>

### prefix_match

#### AC-1: grant id.user.banking satisfies required id.user.banking.view

- AC-1: grant id.user.banking satisfies required id.user.banking.view


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: grant id.user.banking satisfies required id.user.banking.view")
val grant = id_path_intern("id.user.banking")
val required = id_path_intern("id.user.banking.view")
expect id_path_prefix_match(grant, required) to_equal true
```

</details>

#### AC-1: grant id.user.mail does NOT satisfy required id.user.banking

- AC-1: grant id.user.mail does NOT satisfy required id.user.banking


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: grant id.user.mail does NOT satisfy required id.user.banking")
val grant = id_path_intern("id.user.mail")
val required = id_path_intern("id.user.banking")
expect id_path_prefix_match(grant, required) to_equal false
```

</details>

#### AC-1: sibling prefix does not falsely match

- AC-1: sibling prefix does not falsely match


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: sibling prefix does not falsely match")
val grant = id_path_intern("id.user.bank")
val required = id_path_intern("id.user.banking")
expect id_path_prefix_match(grant, required) to_equal false
```

</details>

### subdivide

#### AC-1: parent id.user.banking mints child id.user.banking.view

- AC-1: parent id.user.banking mints child id.user.banking.view


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: parent id.user.banking mints child id.user.banking.view")
val parent = id_path_intern("id.user.banking")
val result = id_path_subdivide(parent, "view")
expect result.ok to_equal true
expect result.value.segments to_contain "view"
```

</details>

#### AC-1: cannot mint unrelated id.user.mail from id.user.banking

- AC-1: cannot mint unrelated id.user.mail from id.user.banking


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: cannot mint unrelated id.user.mail from id.user.banking")
val parent = id_path_intern("id.user.banking")
val result = id_path_subdivide(parent, "id.user.mail")
expect result.ok to_equal false
```

</details>

### segment validation

#### AC-1: segment containing literal dot is rejected

- AC-1: segment containing literal dot is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: segment containing literal dot is rejected")
val parent = id_path_intern("id.user")
val result = id_path_subdivide(parent, "bank.ing")
expect result.ok to_equal false
```

</details>

#### AC-1: empty segment is rejected

- AC-1: empty segment is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: empty segment is rejected")
val parent = id_path_intern("id.user")
val result = id_path_subdivide(parent, "")
expect result.ok to_equal false
```

</details>

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d7a1bfc697ce24a767994f6acd300410696de28b878fb6f2af1a0b5410cc1a96`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d7a1bfc697ce24a767994f6acd300410696de28b878fb6f2af1a0b5410cc1a96`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d7a1bfc697ce24a767994f6acd300410696de28b878fb6f2af1a0b5410cc1a96`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/privilege/id_path_spec.spl
mirror: doc/06_spec/unit/lib/common/privilege/id_path_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/privilege/id_path_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/privilege/id_path_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/privilege/id_path_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: returns identical intern_id for identical strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/privilege/id_path_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: returns distinct intern_id for distinct strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/privilege/id_path_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: splits dotted path into ordered segments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
