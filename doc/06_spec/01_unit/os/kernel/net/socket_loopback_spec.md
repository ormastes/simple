# Socket Loopback Specification

> Tests covering loopback_socket module in isolation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Socket Loopback Specification

## Scenarios

### loopback_socket module in isolation

<details>
<summary>Advanced: detects loopback addresses</summary>

#### detects loopback addresses

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects loopback addresses
   - Expected: loopback_is_loopback_addr(0x0100007Fu32) is true
   - Expected: loopback_is_loopback_addr(0u32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("detects loopback addresses")
clear_loopback_sockets_for_test()
expect(loopback_is_loopback_addr(0x0100007Fu32)).to_equal(true)
expect(loopback_is_loopback_addr(0u32)).to_equal(false)
```

</details>


</details>

#### binds and connects two fds and moves bytes

- binds and connects two fds and moves bytes
   - Expected: bind_rc equals `0`
   - Expected: connect_rc equals `0`
   - Expected: loopback_is_connected(3) is true
   - Expected: loopback_is_connected(4) is true
   - Expected: sent equals `3`
   - Expected: received.len() equals `3u64`
   - Expected: received[0] equals `1u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("binds and connects two fds and moves bytes")
clear_loopback_sockets_for_test()
loopback_register(3)
loopback_register(4)
val bind_rc = loopback_bind(3, 9000u16)
expect(bind_rc).to_equal(0)
val connect_rc = loopback_connect(4, 9000u16)
expect(connect_rc).to_equal(0)
expect(loopback_is_connected(3)).to_equal(true)
expect(loopback_is_connected(4)).to_equal(true)

val sent = loopback_send(4, [1u8, 2u8, 3u8])
expect(sent).to_equal(3)
val received = loopback_recv(3, 64u64)
expect(received.len()).to_equal(3u64)
expect(received[0]).to_equal(1u8)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/net/socket_loopback_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering loopback_socket module in isolation.
- loopback_socket module in isolation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `0d04979d794deae73e7b877bb45d85236a9e83134f204fd8b7f0ca0590522975`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0d04979d794deae73e7b877bb45d85236a9e83134f204fd8b7f0ca0590522975`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0d04979d794deae73e7b877bb45d85236a9e83134f204fd8b7f0ca0590522975`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/os/kernel/net/socket_loopback_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/net/socket_loopback_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/net/socket_loopback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/net/socket_loopback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/net/socket_loopback_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/net/socket_loopback_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects loopback addresses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/net/socket_loopback_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds and connects two fds and moves bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
