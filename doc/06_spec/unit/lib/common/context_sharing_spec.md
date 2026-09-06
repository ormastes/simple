# Context Sharing Specification

> Tests covering Context Sharing (context_def), basic context_def usage, list context, string context, boolean context, reusing contexts, nested contexts with context_def.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Context Sharing Specification

## Scenarios

### Context Sharing (context_def)

### basic context_def usage

#### provides counter value

- provides counter value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides counter value")
expect get_let(:counter) == 0
```

</details>

#### provides increment value

- provides increment value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides increment value")
expect get_let(:increment) == 1
```

</details>

### list context

#### provides items

- provides items


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides items")
val items = get_let(:items)
expect len(items) == 3
```

</details>

#### provides empty list

- provides empty list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides empty list")
val empty = get_let(:empty_list)
expect len(empty) == 0
```

</details>

#### items are accessible

- items are accessible


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("items are accessible")
val items = get_let(:items)
expect items[0] == 1
```

</details>

### string context

#### provides greeting

- provides greeting


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides greeting")
expect get_let(:greeting) == "hello"
```

</details>

#### provides name

- provides name


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides name")
expect get_let(:name) == "world"
```

</details>

### boolean context

#### provides true flag

- provides true flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides true flag")
expect get_let(:flag_true) == true
```

</details>

#### provides false flag

- provides false flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides false flag")
expect get_let(:flag_false) == false
```

</details>

### reusing contexts

#### works first time

- works first time


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works first time")
expect get_let(:counter) == 0
```

</details>

#### works second time

- works second time


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works second time")
expect get_let(:counter) == 0
```

</details>

### nested contexts with context_def

#### outer has items

- outer has items


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("outer has items")
val items = get_let(:items)
expect len(items) == 3
```

</details>

#### inner context

#### inner has extra

- inner has extra


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inner has extra")
expect get_let(:extra) == 99
```

</details>

#### inner still has outer items

- inner still has outer items


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inner still has outer items")
val items = get_let(:items)
expect len(items) == 3
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/context_sharing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Context Sharing (context_def), basic context_def usage, list context, string context, boolean context, reusing contexts, nested contexts with context_def.
- Context Sharing (context_def)
- basic context_def usage
- list context
- string context
- boolean context
- reusing contexts
- nested contexts with context_def

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `7e76477c4ee23beaf1a3c11caacd74c32431ef2dc956fec130ffd60c70c906cf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7e76477c4ee23beaf1a3c11caacd74c32431ef2dc956fec130ffd60c70c906cf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7e76477c4ee23beaf1a3c11caacd74c32431ef2dc956fec130ffd60c70c906cf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/context_sharing_spec.spl
mirror: doc/06_spec/unit/lib/common/context_sharing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/context_sharing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/context_sharing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/context_sharing_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'provides counter value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/context_sharing_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'provides increment value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/context_sharing_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'provides items' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
