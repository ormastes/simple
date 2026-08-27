# Default Param Call Fill Specification

> Tests covering M12 3b: default-param call-site fill.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Default Param Call Fill Specification

## Scenarios

### M12 3b: default-param call-site fill

#### fills a single omitted trailing default

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fills a single omitted trailing default


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fills a single omitted trailing default")
expect greet("hi") == 103
```

</details>

#### keeps explicit trailing args

- keeps explicit trailing args


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps explicit trailing args")
expect greet("hi", 5) == 105
```

</details>

#### fills both omitted defaults

- fills both omitted defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fills both omitted defaults")
expect multi(1) == 31
```

</details>

#### partial fill: one explicit arg, one defaulted

- partial fill: one explicit arg, one defaulted


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("partial fill: one explicit arg, one defaulted")
expect multi(1, 2) == 23
```

</details>

#### all explicit args unchanged

- all explicit args unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all explicit args unchanged")
expect multi(1, 2, 3) == 6
```

</details>

#### no-default function is unaffected

- no-default function is unaffected


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no-default function is unaffected")
expect add(2, 3) == 5
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/default_param_call_fill_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering M12 3b: default-param call-site fill.
- M12 3b: default-param call-site fill

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `bee59b6fc4bed03213c4fe6bcd4c64ff66a9716fde6e058bc530254e547442cf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bee59b6fc4bed03213c4fe6bcd4c64ff66a9716fde6e058bc530254e547442cf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bee59b6fc4bed03213c4fe6bcd4c64ff66a9716fde6e058bc530254e547442cf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/default_param_call_fill_spec.spl
mirror: doc/06_spec/01_unit/compiler/default_param_call_fill_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/default_param_call_fill_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/default_param_call_fill_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/default_param_call_fill_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fills a single omitted trailing default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/default_param_call_fill_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps explicit trailing args' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/default_param_call_fill_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fills both omitted defaults' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
