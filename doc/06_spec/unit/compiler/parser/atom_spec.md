# Atom Specification

> Tests covering atom literals.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Atom Specification

## Scenarios

### atom literals

#### atom is a text value with backtick prefix

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- atom is a text value with backtick prefix
   - Expected: a equals ``hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("atom is a text value with backtick prefix")
val a = make_atom("hello")
expect(a).to_equal("`hello")
```

</details>

#### two atoms with same name are equal

- two atoms with same name are equal
   - Expected: atom_eq(a, b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two atoms with same name are equal")
val a = make_atom("foo")
val b = make_atom("foo")
expect(atom_eq(a, b)).to_equal(true)
```

</details>

#### two atoms with different names are not equal

- two atoms with different names are not equal
   - Expected: not_equal is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two atoms with different names are not equal")
val a = make_atom("foo")
val b = make_atom("bar")
val not_equal = a != b
expect(not_equal).to_equal(true)
```

</details>

#### atom can be used in match

- atom can be used in match
   - Expected: result equals `is running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("atom can be used in match")
val state = make_atom("running")
val result = match state:
    case "`running": "is running"
    case "`stopped": "is stopped"
    case _: "unknown"
expect(result).to_equal("is running")
```

</details>

#### atom used as map key works

- atom used as map key works
   - Expected: m[active] is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("atom used as map key works")
val active = make_atom("active")
val inactive = make_atom("inactive")
val m = {"`active": true, "`inactive": false}
expect(m[active]).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/atom_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering atom literals.
- atom literals

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0eb6b75dc3e59099389a92f40c09416ebefc240fa932abc976f8958f6d2bfba9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0eb6b75dc3e59099389a92f40c09416ebefc240fa932abc976f8958f6d2bfba9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0eb6b75dc3e59099389a92f40c09416ebefc240fa932abc976f8958f6d2bfba9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/parser/atom_spec.spl
mirror: doc/06_spec/unit/compiler/parser/atom_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/parser/atom_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/atom_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/atom_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'atom is a text value with backtick prefix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/atom_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'two atoms with same name are equal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/atom_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'two atoms with different names are not equal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
