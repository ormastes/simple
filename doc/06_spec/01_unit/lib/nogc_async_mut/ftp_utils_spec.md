# Ftp Utils Specification

> Tests covering nogc_async_mut FTP utilities.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ftp Utils Specification

## Scenarios

### nogc_async_mut FTP utilities

#### parses valid PASV response

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses valid PASV response
   - Expected: parsed[0] equals `192.168.1.2`
   - Expected: parsed[1] equals `1930`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses valid PASV response")
val parsed = parse_pasv_response("227 Entering Passive Mode (192,168,1,2,7,138)")
expect(parsed[0]).to_equal("192.168.1.2")
expect(parsed[1]).to_equal(1930)
```

</details>

#### rejects malformed PASV delimiter order

- rejects malformed PASV delimiter order
   - Expected: parsed[0] equals ``
   - Expected: parsed[1] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects malformed PASV delimiter order")
val parsed = parse_pasv_response("227 bad )192,168,1,2,7,138(")
expect(parsed[0]).to_equal("")
expect(parsed[1]).to_equal(0)
```

</details>

#### extract helpers return empty values for malformed PASV response

- extract helpers return empty values for malformed PASV response
   - Expected: extract_pasv_ip("227 bad )1,2,3,4,5,6(") equals ``
   - Expected: extract_pasv_port("227 bad )1,2,3,4,5,6(") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extract helpers return empty values for malformed PASV response")
expect(extract_pasv_ip("227 bad )1,2,3,4,5,6(")).to_equal("")
expect(extract_pasv_port("227 bad )1,2,3,4,5,6(")).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/ftp_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut FTP utilities.
- nogc_async_mut FTP utilities

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `d86005b1c124eed49c3f8512006058d1742d1cb41849210e8eb5071568877b8e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d86005b1c124eed49c3f8512006058d1742d1cb41849210e8eb5071568877b8e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d86005b1c124eed49c3f8512006058d1742d1cb41849210e8eb5071568877b8e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_async_mut/ftp_utils_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/ftp_utils_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/ftp_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/ftp_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/ftp_utils_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/ftp_utils_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses valid PASV response' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/ftp_utils_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects malformed PASV delimiter order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/ftp_utils_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extract helpers return empty values for malformed PASV response' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
