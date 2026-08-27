# String Utils Specification

> Tests covering String Utils.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Utils Specification

## Scenarios

### String Utils

#### trims surrounding whitespace

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- trims surrounding whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trims surrounding whitespace")
val raw = "  build report  "
expect raw.trim() == "build report"
```

</details>

#### detects expected prefixes and suffixes

- detects expected prefixes and suffixes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects expected prefixes and suffixes")
val path = "src/app/tooling/main.spl"
expect path.starts_with("src/app") == true
expect path.ends_with(".spl") == true
```

</details>

#### splits path segments

- splits path segments


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits path segments")
val parts = "src/app/tooling".split("/")
expect parts.len() == 3
expect parts[0] == "src"
expect parts[2] == "tooling"
```

</details>

#### normalizes separators with replace

- normalizes separators with replace


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalizes separators with replace")
val name = "skip test todo"
expect name.replace(" ", "_") == "skip_test_todo"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/string_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering String Utils.
- String Utils

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `7bf8f6c9d4709c072e0ba18a57ce2aa88063f0b5bc23b8534adbd0f1e1d5923d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7bf8f6c9d4709c072e0ba18a57ce2aa88063f0b5bc23b8534adbd0f1e1d5923d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7bf8f6c9d4709c072e0ba18a57ce2aa88063f0b5bc23b8534adbd0f1e1d5923d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/string_utils_spec.spl
mirror: doc/06_spec/unit/app/tooling/string_utils_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/string_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/string_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/string_utils_spec.spl:9:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'trims surrounding whitespace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/string_utils_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects expected prefixes and suffixes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/string_utils_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'splits path segments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
