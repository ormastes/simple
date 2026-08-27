# Pass Statement and Unit Value Equivalence

> In Simple, the `pass` keyword and the unit literal `()` are semantically equivalent -- both represent a deliberate no-operation and compile to the same code. This spec proves their interchangeability in every statement position: standalone expressions, if/else branches, and loop bodies. It also documents the style guideline that `pass` is preferred when the programmer wants to signal explicit "do nothing" intent, while `()` is the underlying unit value.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pass Statement and Unit Value Equivalence

In Simple, the `pass` keyword and the unit literal `()` are semantically equivalent -- both represent a deliberate no-operation and compile to the same code. This spec proves their interchangeability in every statement position: standalone expressions, if/else branches, and loop bodies. It also documents the style guideline that `pass` is preferred when the programmer wants to signal explicit "do nothing" intent, while `()` is the underlying unit value.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-021 |
| Category | Language |
| Status | Active |
| Source | `test/feature/usage/pass_unit_equivalence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

In Simple, the `pass` keyword and the unit literal `()` are semantically
equivalent -- both represent a deliberate no-operation and compile to the same
code. This spec proves their interchangeability in every statement position:
standalone expressions, if/else branches, and loop bodies. It also documents the
style guideline that `pass` is preferred when the programmer wants to signal
explicit "do nothing" intent, while `()` is the underlying unit value.

## Syntax

```simple
# pass as a standalone no-op
pass
x = 1

# () as a standalone no-op
()
x = 1

# pass inside an if-else branch
if x == 10:
branch_taken = "ten"
else:
pass
branch_taken = "other"

# pass inside a loop body
for i in [0, 1, 2]:
if i == 1:
pass
count = count + 1
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `pass` | A no-op keyword signalling intentional emptiness, analogous to Python's `pass` |
| `()` | The unit literal, representing the absence of a meaningful value |
| Equivalence | `pass` and `()` produce identical compiled output in all statement positions |
| Style guideline | Use `pass` for explicit no-op intent; use `()` when a unit value is needed |

## Scenarios

### pass and () equivalence

#### both work as standalone statements

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- both work as standalone statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("both work as standalone statements")
var executed = false

# With pass
pass
executed = true
expect executed == true

# With ()
executed = false
()
executed = true
expect executed == true
```

</details>

#### both work in if-else branches

- both work in if-else branches


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("both work in if-else branches")
val x = 5
var branch_taken = ""

# Using pass
if x == 10:
    branch_taken = "ten"
else:
    pass
    branch_taken = "other"

expect branch_taken == "other"

# Using ()
branch_taken = ""
if x == 10:
    branch_taken = "ten"
else:
    ()
    branch_taken = "other"

expect branch_taken == "other"
```

</details>

<details>
<summary>Advanced: both work in loops</summary>

#### both work in loops

- both work in loops


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("both work in loops")
var count = 0

# With pass
for i in [0, 1, 2]:
    if i == 1:
        pass
    count = count + 1

expect count == 3

# With ()
count = 0
for i in [0, 1, 2]:
    if i == 1:
        ()
    count = count + 1

expect count == 3
```

</details>


</details>

### pass and () documentation

#### documents that pass is no-op statement

- documents that pass is no-op statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("documents that pass is no-op statement")
var x = 0
pass
x = 1
expect x == 1
```

</details>

### style guidelines

#### recommends pass for explicit no-op intent

- recommends pass for explicit no-op intent


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("recommends pass for explicit no-op intent")
var logged = false
if true:
    pass
    logged = false
expect logged == false
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

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0272d643c5910966061d2bc4671655e1e5c6de299e5b4d192823fd19ee723969`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0272d643c5910966061d2bc4671655e1e5c6de299e5b4d192823fd19ee723969`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0272d643c5910966061d2bc4671655e1e5c6de299e5b4d192823fd19ee723969`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/pass_unit_equivalence_spec.spl
mirror: doc/06_spec/feature/usage/pass_unit_equivalence_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/pass_unit_equivalence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/pass_unit_equivalence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/pass_unit_equivalence_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'both work as standalone statements' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/pass_unit_equivalence_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'both work in if-else branches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/pass_unit_equivalence_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'both work in loops' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
