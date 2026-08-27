# rv64_boot_gate_runtime_spec

> Runtime-result adapter for the RV64 lifecycle gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rv64_boot_gate_runtime_spec

Runtime-result adapter for the RV64 lifecycle gate.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/rv64_boot_gate_runtime_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Runtime-result adapter for the RV64 lifecycle gate.

## Scenarios

### RV64 runtime boot-gate adapter

#### rejects SATP PPN bits that disagree with the separately decoded PPN

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects SATP PPN bits that disagree with the separately decoded PPN
   - Expected: gate.verdict() equals `FAIL:sv39-readback-unproven`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects SATP PPN bits that disagree with the separately decoded PPN")
var gate = Rv64BootGateRuntime.create()
gate.observe_sv39(Rv64Sv39ActivationResult(root_phys: 0x81000000, satp_value: 0x8000000000082000, satp_mode: 8, satp_root_ppn: 0x81000, active: true))
expect(gate.verdict()).to_equal("FAIL:sv39-readback-unproven")
```

</details>

#### rejects a decoded Sv39 mode that disagrees with the SATP mode bits

- rejects a decoded Sv39 mode that disagrees with the SATP mode bits
   - Expected: gate.verdict() equals `FAIL:sv39-readback-unproven`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a decoded Sv39 mode that disagrees with the SATP mode bits")
var gate = Rv64BootGateRuntime.create()
gate.observe_sv39(Rv64Sv39ActivationResult(root_phys: 0x81000000, satp_value: 0x9000000000081000, satp_mode: 8, satp_root_ppn: 0x81000, active: true))
expect(gate.verdict()).to_equal("FAIL:sv39-readback-unproven")
```

</details>

#### rejects an unaligned root even when its truncated PPN matches SATP

- rejects an unaligned root even when its truncated PPN matches SATP
   - Expected: gate.verdict() equals `FAIL:sv39-readback-unproven`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unaligned root even when its truncated PPN matches SATP")
var gate = Rv64BootGateRuntime.create()
gate.observe_sv39(Rv64Sv39ActivationResult(root_phys: 0x81000001, satp_value: 0x8000000000081000, satp_mode: 8, satp_root_ppn: 0x81000, active: true))
expect(gate.verdict()).to_equal("FAIL:sv39-readback-unproven")
```

</details>

#### remains incomplete without a production WM process/present verdict

- remains incomplete without a production WM process/present verdict
   - Expected: gate.verdict() equals `INCOMPLETE:missing=wm-process-owned-frame-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remains incomplete without a production WM process/present verdict")
val gate = runtime_through_first_ssh_resume()
expect(gate.verdict()).to_equal("INCOMPLETE:missing=wm-process-owned-frame-ready")
```

</details>

#### fails closed when the production WM producer is unavailable

- fails closed when the production WM producer is unavailable
   - Expected: gate.verdict() equals `FAIL:wm-production-launch-and-engine2d-present-producer-missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed when the production WM producer is unavailable")
var gate = runtime_through_first_ssh_resume()
gate.block_missing_wm_producer()
expect(gate.verdict()).to_equal("FAIL:wm-production-launch-and-engine2d-present-producer-missing")
```

</details>

#### rejects an SSH accept without completed session recovery

- rejects an SSH accept without completed session recovery
   - Expected: gate.verdict() equals `FAIL:sshd-session-incomplete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an SSH accept without completed session recovery")
var gate = Rv64BootGateRuntime.create()
gate.observe_sv39(Rv64Sv39ActivationResult(root_phys: 0x81000000, satp_value: 0x8000000000081000, satp_mode: 8, satp_root_ppn: 0x81000, active: true))
gate.observe_pid1(Rv64Pid1BootResult(created: true, live: true, pid: 1))
gate.observe_network(RiscvNetworkBootFacts(tx_ready: true, rx_ready: true, service_ready: true))
gate.observe_sshd_ready(true)
gate.observe_ssh_progress(SshDaemonAcceptResult(accepted: true, session_complete: false, accept_resumed: false))
expect(gate.verdict()).to_equal("FAIL:sshd-session-incomplete")
```

</details>

#### keeps validating accept recovery after the ordered SSH receipt

- keeps validating accept recovery after the ordered SSH receipt
   - Expected: gate.verdict() equals `FAIL:sshd-later-accept-not-resumed`
   - Expected: gate.verdict() equals `FAIL:sshd-later-accept-not-resumed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps validating accept recovery after the ordered SSH receipt")
var gate = runtime_through_first_ssh_resume()
val broken = SshDaemonAcceptResult(accepted: true, session_complete: true, accept_resumed: false)
expect(gate.observe_ssh_progress(broken)).to_be(false)
expect(gate.verdict()).to_equal("FAIL:sshd-later-accept-not-resumed")
val recovered = SshDaemonAcceptResult(accepted: true, session_complete: true, accept_resumed: true)
expect(gate.observe_ssh_progress(recovered)).to_be(false)
expect(gate.verdict()).to_equal("FAIL:sshd-later-accept-not-resumed")
```

</details>

#### fails closed when a later accepted session does not complete

- fails closed when a later accepted session does not complete
   - Expected: gate.verdict() equals `FAIL:sshd-later-session-incomplete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed when a later accepted session does not complete")
var gate = runtime_through_first_ssh_resume()
val incomplete = SshDaemonAcceptResult(accepted: true, session_complete: false, accept_resumed: false)
expect(gate.observe_ssh_progress(incomplete)).to_be(false)
expect(gate.verdict()).to_equal("FAIL:sshd-later-session-incomplete")
```

</details>

<details>
<summary>Advanced: keeps a completed later auth attempt in the accept loop</summary>

#### keeps a completed later auth attempt in the accept loop

- keeps a completed later auth attempt in the accept loop
   - Expected: gate.verdict() equals `INCOMPLETE:missing=wm-process-owned-frame-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a completed later auth attempt in the accept loop")
var gate = runtime_through_first_ssh_resume()
val completed = SshDaemonAcceptResult(accepted: true, session_complete: true, accept_resumed: true)
expect(gate.observe_ssh_progress(completed)).to_be(true)
expect(gate.verdict()).to_equal("INCOMPLETE:missing=wm-process-owned-frame-ready")
```

</details>


</details>

#### reaches terminal PASS only from the one production WM receipt

- reaches terminal PASS only from the one production WM receipt
   - Expected: gate.verdict() equals `PASS`
   - Expected: gate.verdict() equals `PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reaches terminal PASS only from the one production WM receipt")
var gate = runtime_through_first_ssh_resume()
val wm = Rv64ProductionWmVerdict(ready: true, failed: false, process_id: 41u64, first_present_revision: 7, reason: "ready")
expect(gate.observe_wm(wm)).to_be(true)
expect(gate.verdict()).to_equal("PASS")
val later = SshDaemonAcceptResult(accepted: true, session_complete: true, accept_resumed: true)
expect(gate.observe_ssh_progress(later)).to_be(true)
expect(gate.verdict()).to_equal("PASS")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `003177f04d6761ff7a63e85e9d67484775e716fc46310e63f6103b34cf35d443`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `003177f04d6761ff7a63e85e9d67484775e716fc46310e63f6103b34cf35d443`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `003177f04d6761ff7a63e85e9d67484775e716fc46310e63f6103b34cf35d443`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/rv64_boot_gate_runtime_spec.spl
mirror: doc/06_spec/01_unit/os/rv64_boot_gate_runtime_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/rv64_boot_gate_runtime_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/rv64_boot_gate_runtime_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/rv64_boot_gate_runtime_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects SATP PPN bits that disagree with the separately decoded PPN' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/rv64_boot_gate_runtime_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a decoded Sv39 mode that disagrees with the SATP mode bits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/rv64_boot_gate_runtime_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an unaligned root even when its truncated PPN matches SATP' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
