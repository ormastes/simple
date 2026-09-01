# Discovery Specification

> Tests covering Doctest Source Parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Discovery Specification

## Scenarios

### Doctest Source Parsing

#### parse_doctests integration

#### discovers doctests in doc comments

- discovers doctests in doc comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers doctests in doc comments")
val source = "/// Example usage:\n/// >>> 1 + 2\n/// 3\nfn add(a: i64, b: i64) -> i64:\n    a + b\n"
val items = parse_doctests(source, "lib/math.spl")

expect items.len to eq 1
expect items[0].commands to eq ["1 + 2"]
expect items[0].source_path to eq "lib/math.spl"
```

</details>

#### discovers multiple doctests across functions

- discovers multiple doctests across functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers multiple doctests across functions")
val source = "/// >>> 1 + 1\n/// 2\nfn foo(): pass\n\n/// >>> 2 + 2\n/// 4\nfn bar(): pass\n"
val items = parse_doctests(source, "lib/ops.spl")

expect items.len to eq 2
expect items[0].commands to eq ["1 + 1"]
expect items[1].commands to eq ["2 + 2"]
```

</details>

#### skips functions without doc comments

- skips functions without doc comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("skips functions without doc comments")
val source = "fn helper(): pass\n\n/// >>> 42\n/// 42\nfn documented(): pass\n"
val items = parse_doctests(source, "lib/mixed.spl")

expect items.len to eq 1
expect items[0].commands to eq ["42"]
```

</details>

#### handles exception expectations in doc comments

- handles exception expectations in doc comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles exception expectations in doc comments")
val source = "/// >>> bad_call()\n/// Error: ValueError\nfn risky(): pass\n"
val items = parse_doctests(source, "lib/errors.spl")

expect items.len to eq 1
match items[0].expected:
    case Expected.Exception(type, msg):
        expect type to eq "ValueError"
    case _:
        fail "Expected Exception"
```

</details>

#### preserves line numbers

- preserves line numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preserves line numbers")
val source = "# header\n\n/// >>> 1\n/// 1\nfn f(): pass\n"
val items = parse_doctests(source, "test.spl")

expect items.len to eq 1
expect items[0].start_line to eq 3
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/std/doctest/discovery_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Doctest Source Parsing.
- Doctest Source Parsing

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4590d7fd1ae229e123089ac1ec66bbf69a3d94a7bda13dae4c18a90a6864cda2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4590d7fd1ae229e123089ac1ec66bbf69a3d94a7bda13dae4c18a90a6864cda2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4590d7fd1ae229e123089ac1ec66bbf69a3d94a7bda13dae4c18a90a6864cda2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/lib/std/doctest/discovery_spec.spl
mirror: doc/06_spec/02_integration/lib/std/doctest/discovery_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/lib/std/doctest/discovery_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/std/doctest/discovery_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/lib/std/doctest/discovery_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'discovers doctests in doc comments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/std/doctest/discovery_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'discovers multiple doctests across functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/std/doctest/discovery_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips functions without doc comments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
