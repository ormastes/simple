# Long Literal Local Val Aliasing Probe Specification

> Tests covering long string literal duplicated across functions in one module.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Long Literal Local Val Aliasing Probe Specification

## Scenarios

### long string literal duplicated across functions in one module

#### identity across binding styles

#### the directly-returned literal has the expected length

- the directly-returned literal has the expected length
   - Expected: _literal_returned_directly().length() equals `187`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("the directly-returned literal has the expected length")
expect(_literal_returned_directly().length()).to_equal(187)
```

</details>

#### the local-val-bound literal has the expected length

- the local-val-bound literal has the expected length
   - Expected: _literal_via_local_val().length() equals `187`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("the local-val-bound literal has the expected length")
expect(_literal_via_local_val().length()).to_equal(187)
```

</details>

#### both binding styles yield the same text

- both binding styles yield the same text
   - Expected: _literal_via_local_val() equals `_literal_returned_directly()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("both binding styles yield the same text")
expect(_literal_via_local_val()).to_equal(_literal_returned_directly())
```

</details>

#### a split-and-rejoin of the local-val copy reconstructs the original

- a split-and-rejoin of the local-val copy reconstructs the original
   - Expected: _literal_sliced_via_local_val() equals `_literal_returned_directly()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a split-and-rejoin of the local-val copy reconstructs the original")
expect(_literal_sliced_via_local_val()).to_equal(_literal_returned_directly())
```

</details>

#### prefix and interior are not corrupted

#### keeps its header

- keeps its header
   - Expected: _literal_via_local_val().substring(0, 9) equals `v4.local.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps its header")
expect(_literal_via_local_val().substring(0, 9)).to_equal("v4.local.")
```

</details>

#### agrees with the direct copy at the index the old fixture mutated

- agrees with the direct copy at the index the old fixture mutated


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("agrees with the direct copy at the index the old fixture mutated")
expect(_literal_via_local_val().substring(15, 16)).to_equal(
    _literal_returned_directly().substring(15, 16)
)
```

</details>

#### agrees with the direct copy on its final characters

- agrees with the direct copy on its final characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("agrees with the direct copy on its final characters")
val a = _literal_via_local_val()
val b = _literal_returned_directly()
expect(a.substring(a.length() - 4, a.length())).to_equal(
    b.substring(b.length() - 4, b.length())
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/long_literal_local_val_aliasing_probe_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering long string literal duplicated across functions in one module.
- long string literal duplicated across functions in one module

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `55fd8e20cfaa58176a5344e3b9e3e07449bd5f0d39d67210dd31908668252d13`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `55fd8e20cfaa58176a5344e3b9e3e07449bd5f0d39d67210dd31908668252d13`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `55fd8e20cfaa58176a5344e3b9e3e07449bd5f0d39d67210dd31908668252d13`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/interpreter/long_literal_local_val_aliasing_probe_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/long_literal_local_val_aliasing_probe_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/long_literal_local_val_aliasing_probe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/long_literal_local_val_aliasing_probe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/long_literal_local_val_aliasing_probe_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/long_literal_local_val_aliasing_probe_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the directly-returned literal has the expected length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/long_literal_local_val_aliasing_probe_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the local-val-bound literal has the expected length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/long_literal_local_val_aliasing_probe_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'both binding styles yield the same text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
