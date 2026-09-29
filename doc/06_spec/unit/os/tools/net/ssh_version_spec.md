# SSH Version String Specification

> Verifies that the SSH version string builder produces the correct RFC 4253 identification string: "SSH-2.0-SimpleOS_1.0\\r\\n".

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SSH Version String Specification

Verifies that the SSH version string builder produces the correct RFC 4253 identification string: "SSH-2.0-SimpleOS_1.0\\r\\n".

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SSH1 |
| Category | Infrastructure |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/unit/os/tools/net/ssh_version_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the SSH version string builder produces the correct
RFC 4253 identification string: "SSH-2.0-SimpleOS_1.0\\r\\n".

## Scenarios

### ssh_build_version_string

#### produces exactly 22 bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces exactly 22 bytes
   - Expected: buf.len() equals `22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces exactly 22 bytes")
var buf: [u8] = ssh_build_version_string()
expect(buf.len()).to_equal(22)
```

</details>

#### starts with SSH-2.0-SimpleOS_1.0

- starts with SSH-2.0-SimpleOS_1.0
   - Expected: buf[0] equals `0x53`
   - Expected: buf[1] equals `0x53`
   - Expected: buf[2] equals `0x48`
   - Expected: buf[3] equals `0x2D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with SSH-2.0-SimpleOS_1.0")
var buf: [u8] = ssh_build_version_string()
# S=0x53, S=0x53, H=0x48, -=0x2D
expect(buf[0]).to_equal(0x53)
expect(buf[1]).to_equal(0x53)
expect(buf[2]).to_equal(0x48)
expect(buf[3]).to_equal(0x2D)
```

</details>

#### ends with CR LF

- ends with CR LF
   - Expected: buf[20] equals `0x0D`
   - Expected: buf[21] equals `0x0A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ends with CR LF")
var buf: [u8] = ssh_build_version_string()
expect(buf[20]).to_equal(0x0D)
expect(buf[21]).to_equal(0x0A)
```

</details>

#### contains version 2.0 marker bytes

- contains version 2.0 marker bytes
   - Expected: buf[4] equals `0x32`
   - Expected: buf[5] equals `0x2E`
   - Expected: buf[6] equals `0x30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains version 2.0 marker bytes")
var buf: [u8] = ssh_build_version_string()
# '2'=0x32, '.'=0x2E, '0'=0x30
expect(buf[4]).to_equal(0x32)
expect(buf[5]).to_equal(0x2E)
expect(buf[6]).to_equal(0x30)
```

</details>

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

- Canonical SPipe generation for source `a6265137157f91e35e1a4bcb53e46d950e9cdb79e3b73a1c2a2bdac6ff5d386e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a6265137157f91e35e1a4bcb53e46d950e9cdb79e3b73a1c2a2bdac6ff5d386e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a6265137157f91e35e1a4bcb53e46d950e9cdb79e3b73a1c2a2bdac6ff5d386e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/os/tools/net/ssh_version_spec.spl
mirror: doc/06_spec/unit/os/tools/net/ssh_version_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/tools/net/ssh_version_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/tools/net/ssh_version_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/tools/net/ssh_version_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/tools/net/ssh_version_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces exactly 22 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tools/net/ssh_version_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts with SSH-2.0-SimpleOS_1.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tools/net/ssh_version_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ends with CR LF' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
