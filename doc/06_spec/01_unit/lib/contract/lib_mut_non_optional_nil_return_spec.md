# Lib Mut Non Optional Nil Return Specification

> Tests covering non-optional return contract fixes (nil path).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lib Mut Non Optional Nil Return Specification

## Scenarios

### non-optional return contract fixes (nil path)

#### get_header returns nil (not a crash) when the header is absent

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- get_header returns nil (not a crash) when the header is absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("get_header returns nil (not a crash) when the header is absent")
val headers = [("Content-Type", "text/plain")]
expect get_header(headers, "X-Missing") == nil
```

</details>

#### parse_range_header returns nil on a malformed Range header

- parse_range_header returns nil on a malformed Range header


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parse_range_header returns nil on a malformed Range header")
expect parse_range_header("not-a-range") == nil
```

</details>

#### parse_multipart_part returns nil when no header/body separator is found

- parse_multipart_part returns nil when no header/body separator is found


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parse_multipart_part returns nil when no header/body separator is found")
expect parse_multipart_part("no-crlf-separator-here") == nil
```

</details>

#### get_query_param returns nil when the parameter name is absent

- get_query_param returns nil when the parameter name is absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("get_query_param returns nil when the parameter name is absent")
expect get_query_param([("a", "1"), ("b", "2")], "missing") == nil
```

</details>

#### mailbox_receive returns nil when the mailbox is empty

- mailbox_receive returns nil when the mailbox is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("mailbox_receive returns nil when the mailbox is empty")
val mb = mailbox_new(4)
expect mailbox_receive(mb) == nil
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/contract/lib_mut_non_optional_nil_return_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering non-optional return contract fixes (nil path).
- non-optional return contract fixes (nil path)

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3026f2a2c9608c8e524cad2c114d5eb8ee55df5ada5bc33f560db652b67a1835`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3026f2a2c9608c8e524cad2c114d5eb8ee55df5ada5bc33f560db652b67a1835`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3026f2a2c9608c8e524cad2c114d5eb8ee55df5ada5bc33f560db652b67a1835`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/contract/lib_mut_non_optional_nil_return_spec.spl
mirror: doc/06_spec/01_unit/lib/contract/lib_mut_non_optional_nil_return_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=80 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/contract/lib_mut_non_optional_nil_return_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/contract/lib_mut_non_optional_nil_return_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/contract/lib_mut_non_optional_nil_return_spec.spl:1:1: advice SSDOC-COV-001 [coverage] (-20): the authored requirement defines adverse behavior but no adverse scenario is named
  why: Specifications should explain behavior outside the happy path.
  improve: Add adverse-path scenarios required by the source, or record a reasoned suppression.
test/01_unit/lib/contract/lib_mut_non_optional_nil_return_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'get_header returns nil (not a crash) when the header is absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/contract/lib_mut_non_optional_nil_return_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parse_range_header returns nil on a malformed Range header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/contract/lib_mut_non_optional_nil_return_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parse_multipart_part returns nil when no header/body separator is found' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
