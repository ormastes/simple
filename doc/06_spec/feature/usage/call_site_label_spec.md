# Call-Site Argument Labels

> Call-site labels are postfix keywords attached to arguments at the call site that improve readability of function calls by making the role of each argument explicit. Labels such as `to`, `from`, `by`, `into`, `onto`, and `with` are declared on parameter definitions and optionally used at the call site. Labels are purely syntactic sugar for documentation purposes -- the argument is still matched by position, and omitting the label is valid. This spec validates all six built-in labels, label-free calling, and multi-label combinations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Call-Site Argument Labels

Call-site labels are postfix keywords attached to arguments at the call site that improve readability of function calls by making the role of each argument explicit. Labels such as `to`, `from`, `by`, `into`, `onto`, and `with` are declared on parameter definitions and optionally used at the call site. Labels are purely syntactic sugar for documentation purposes -- the argument is still matched by position, and omitting the label is valid. This spec validates all six built-in labels, label-free calling, and multi-label combinations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYNTAX-012 |
| Category | Syntax |
| Status | Active |
| Source | `test/feature/usage/call_site_label_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Call-site labels are postfix keywords attached to arguments at the call site that improve
readability of function calls by making the role of each argument explicit. Labels such
as `to`, `from`, `by`, `into`, `onto`, and `with` are declared on parameter definitions
and optionally used at the call site. Labels are purely syntactic sugar for documentation
purposes -- the argument is still matched by position, and omitting the label is valid.
This spec validates all six built-in labels, label-free calling, and multi-label
combinations.

## Syntax

```simple
use std.spec.step

fn copy_item(src to, dst):
dst
val result = copy_item("a" to, "b")

fn scale(value, factor by):
value * factor
val result = scale(10, 3 by)

fn transfer(amount, src from, dst to):
amount
val result = transfer(100, "checking" from, "savings" to)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Call-Site Label | A postfix keyword (`to`, `from`, `by`, `into`, `onto`, `with`) on an argument |
| Parameter Label | Declared in the function signature after the parameter name |
| Optional Usage | Labels can be omitted at the call site; arguments match by position |
| Multiple Labels | A single function can use different labels on different parameters |

## Scenarios

### Call-site labels

#### basic label usage

#### allows to label

- allows to label


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows to label")
fn copy_item(src to, dst):
    dst
val result = copy_item("a" to, "b")
expect result == "b"
```

</details>

#### allows from label

- allows from label


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows from label")
fn fetch(url, origin from):
    origin
val result = fetch("http://example.com", "localhost" from)
expect result == "localhost"
```

</details>

#### allows by label

- allows by label


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows by label")
fn scale(value, factor by):
    value * factor
val result = scale(10, 3 by)
expect result == 30
```

</details>

#### allows into label

- allows into label


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows into label")
fn convert(data, fmt into):
    fmt
val result = convert("raw", "json" into)
expect result == "json"
```

</details>

#### allows onto label

- allows onto label


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows onto label")
fn place(item, target onto):
    target
val result = place("widget", "canvas" onto)
expect result == "canvas"
```

</details>

#### allows with label

- allows with label


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows with label")
fn open_file(path, mode with):
    mode
val result = open_file("/tmp/f", "rw" with)
expect result == "rw"
```

</details>

#### no label cases

#### works without labels

- works without labels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works without labels")
fn add(a, b):
    a + b
val result = add(3, 4)
expect result == 7
```

</details>

#### works with label on param but no label on arg

- works with label on param but no label on arg


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with label on param but no label on arg")
fn copy_item2(src to, dst):
    dst
val result = copy_item2("a", "b")
expect result == "b"
```

</details>

#### multiple labels

#### supports from and to labels together

- supports from and to labels together


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("supports from and to labels together")
fn transfer(amount, src from, dst to):
    amount
val result = transfer(100, "checking" from, "savings" to)
expect result == 100
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `a7a68d62df5ba05437960a7b683cac67311960ed86020c342cfd74fc4ad12e03`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a7a68d62df5ba05437960a7b683cac67311960ed86020c342cfd74fc4ad12e03`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a7a68d62df5ba05437960a7b683cac67311960ed86020c342cfd74fc4ad12e03`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/call_site_label_spec.spl
mirror: doc/06_spec/feature/usage/call_site_label_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/call_site_label_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/call_site_label_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/call_site_label_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows to label' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/call_site_label_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows from label' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/call_site_label_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows by label' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
