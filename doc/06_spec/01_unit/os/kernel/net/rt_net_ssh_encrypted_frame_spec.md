# Rt Net Ssh Encrypted Frame Specification

> Tests covering SSH encrypted socket read admission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rt Net Ssh Encrypted Frame Specification

## Scenarios

### SSH encrypted socket read admission

#### admits the minimum and maximum body before reading the remainder

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- admits the minimum and maximum body before reading the remainder
   - Expected: minimum.unwrap().remaining_read_bytes equals `18`
   - Expected: minimum.unwrap().total_frame_bytes equals `22`
   - Expected: maximum.unwrap().advertised_body_bytes equals `35000`
   - Expected: maximum.unwrap().remaining_read_bytes equals `35016`
   - Expected: maximum.unwrap().total_frame_bytes equals `35020`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("admits the minimum and maximum body before reading the remainder")
val minimum = rt_net_ssh_encrypted_read_plan(2u32)
val maximum = rt_net_ssh_encrypted_read_plan(35000u32)
expect(minimum == nil).to_be(false)
expect(maximum == nil).to_be(false)
if minimum != nil:
    expect(minimum.unwrap().remaining_read_bytes).to_equal(18)
    expect(minimum.unwrap().total_frame_bytes).to_equal(22)
if maximum != nil:
    expect(maximum.unwrap().advertised_body_bytes).to_equal(35000)
    expect(maximum.unwrap().remaining_read_bytes).to_equal(35016)
    expect(maximum.unwrap().total_frame_bytes).to_equal(35020)
```

</details>

#### refuses invalid and oversized bodies without a read plan

- refuses invalid and oversized bodies without a read plan


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("refuses invalid and oversized bodies without a read plan")
expect(rt_net_ssh_encrypted_read_plan(0u32)).to_be_nil()
expect(rt_net_ssh_encrypted_read_plan(1u32)).to_be_nil()
expect(rt_net_ssh_encrypted_read_plan(35001u32)).to_be_nil()
expect(rt_net_ssh_encrypted_read_plan(262144u32)).to_be_nil()
```

</details>

#### routes reads only through the requested socket owner

- routes reads only through the requested socket owner
   - Expected: rt_net_resolve_socket_read_owner(1001, first).unwrap() equals `200`
   - Expected: rt_net_resolve_socket_read_owner(1002, second).unwrap() equals `201`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("routes reads only through the requested socket owner")
val first = RtNetSocketReadOwner(socket_fd: 1001, os_fd: 200)
val second = RtNetSocketReadOwner(socket_fd: 1002, os_fd: 201)
expect(rt_net_resolve_socket_read_owner(1001, first).unwrap()).to_equal(200)
expect(rt_net_resolve_socket_read_owner(1002, first)).to_be_nil()
expect(rt_net_resolve_socket_read_owner(1002, second).unwrap()).to_equal(201)
expect(rt_net_resolve_socket_read_owner(1001, RtNetSocketReadOwner(socket_fd: 1001, os_fd: -1))).to_be_nil()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/net/rt_net_ssh_encrypted_frame_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SSH encrypted socket read admission.
- SSH encrypted socket read admission

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8c1a48acea3d3f0e5d6c4313d82a14c7f3d18991d68fcb3c629b523681f76072`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8c1a48acea3d3f0e5d6c4313d82a14c7f3d18991d68fcb3c629b523681f76072`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8c1a48acea3d3f0e5d6c4313d82a14c7f3d18991d68fcb3c629b523681f76072`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/kernel/net/rt_net_ssh_encrypted_frame_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/net/rt_net_ssh_encrypted_frame_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/net/rt_net_ssh_encrypted_frame_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/net/rt_net_ssh_encrypted_frame_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/net/rt_net_ssh_encrypted_frame_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/net/rt_net_ssh_encrypted_frame_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits the minimum and maximum body before reading the remainder' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/net/rt_net_ssh_encrypted_frame_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses invalid and oversized bodies without a read plan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/net/rt_net_ssh_encrypted_frame_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes reads only through the requested socket owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
