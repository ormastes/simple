# rv64_boot_gate_spec

> Pure fail-closed RV64 boot lifecycle admission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rv64_boot_gate_spec

Pure fail-closed RV64 boot lifecycle admission.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/rv64_boot_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure fail-closed RV64 boot lifecycle admission.

## Scenarios

### RV64 boot gate state machine

#### accepts the exact ordered lifecycle

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts the exact ordered lifecycle
   - Expected: rv64_boot_gate_verdict(state) equals `PASS`
   - Expected: state.accepted_count equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts the exact ordered lifecycle")
val state = advance_happy_path()
expect(rv64_boot_gate_verdict(state)).to_equal("PASS")
expect(state.accepted_count).to_equal(9)
expect(state.terminal).to_be(true)
```

</details>

#### reports the first missing lifecycle observation

- reports the first missing lifecycle observation
   - Expected: rv64_boot_gate_verdict(state) equals `INCOMPLETE:missing=network-tx-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reports the first missing lifecycle observation")
var state = rv64_boot_gate_new()
state = rv64_boot_gate_advance(state, Rv64BootGateObservation.Sv39Active)
state = rv64_boot_gate_advance(state, Rv64BootGateObservation.Pid1Live)
expect(rv64_boot_gate_verdict(state)).to_equal("INCOMPLETE:missing=network-tx-ready")
```

</details>

#### rejects a reordered observation and retains that first error

- rejects a reordered observation and retains that first error
   - Expected: first equals `FAIL:reordered:expected=pid1-live:observed=network-tx-ready`
   - Expected: rv64_boot_gate_verdict(state) equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a reordered observation and retains that first error")
var state = rv64_boot_gate_new()
state = rv64_boot_gate_advance(state, Rv64BootGateObservation.Sv39Active)
state = rv64_boot_gate_advance(state, Rv64BootGateObservation.NetworkTxReady)
val first = rv64_boot_gate_verdict(state)
state = rv64_boot_gate_advance(state, Rv64BootGateObservation.Pid1Live)
expect(first).to_equal("FAIL:reordered:expected=pid1-live:observed=network-tx-ready")
expect(rv64_boot_gate_verdict(state)).to_equal(first)
```

</details>

#### rejects a duplicate observation and retains that first error

- rejects a duplicate observation and retains that first error
   - Expected: first equals `FAIL:duplicate-or-replayed:sv39-active`
   - Expected: rv64_boot_gate_verdict(state) equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a duplicate observation and retains that first error")
var state = rv64_boot_gate_new()
state = rv64_boot_gate_advance(state, Rv64BootGateObservation.Sv39Active)
state = rv64_boot_gate_advance(state, Rv64BootGateObservation.Sv39Active)
val first = rv64_boot_gate_verdict(state)
state = rv64_boot_gate_advance(state, Rv64BootGateObservation.Pid1Live)
expect(first).to_equal("FAIL:duplicate-or-replayed:sv39-active")
expect(rv64_boot_gate_verdict(state)).to_equal(first)
```

</details>

#### rejects observations after the terminal lifecycle receipt

- rejects observations after the terminal lifecycle receipt
   - Expected: rv64_boot_gate_verdict(state) equals `FAIL:post-terminal:wm-process-owned-frame-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects observations after the terminal lifecycle receipt")
var state = advance_happy_path()
state = rv64_boot_gate_advance(state, Rv64BootGateObservation.WmProcessOwnedFrameReady)
expect(rv64_boot_gate_verdict(state)).to_equal("FAIL:post-terminal:wm-process-owned-frame-ready")
```

</details>

### RV64 boot gate transcript checker

#### accepts canonical receipts while ignoring unrelated serial lines

- accepts canonical receipts while ignoring unrelated serial lines
   - Expected: check_rv64_boot_gate_transcript(lines) equals `PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts canonical receipts while ignoring unrelated serial lines")
var lines: [text] = ["OpenSBI v1", "MEM OK"]
for receipt in prepare_rv64_boot_gate_fixture():
    lines.push(receipt)
lines.push("OS IDLE")
expect(check_rv64_boot_gate_transcript(lines)).to_equal("PASS")
```

</details>

#### fails closed for a missing canonical receipt

- fails closed for a missing canonical receipt
   - Expected: check_rv64_boot_gate_transcript(lines) equals `INCOMPLETE:missing=network-tx-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed for a missing canonical receipt")
val lines = [
    RV64_BOOT_GATE_RECEIPT_PREFIX + RV64_BOOT_GATE_SV39_ACTIVE,
    RV64_BOOT_GATE_RECEIPT_PREFIX + RV64_BOOT_GATE_PID1_LIVE
]
expect(check_rv64_boot_gate_transcript(lines)).to_equal("INCOMPLETE:missing=network-tx-ready")
```

</details>

#### rejects duplicate canonical receipts

- rejects duplicate canonical receipts
   - Expected: check_rv64_boot_gate_transcript(lines) equals `FAIL:duplicate-or-replayed:sv39-active`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects duplicate canonical receipts")
val lines = [
    RV64_BOOT_GATE_RECEIPT_PREFIX + RV64_BOOT_GATE_SV39_ACTIVE,
    RV64_BOOT_GATE_RECEIPT_PREFIX + RV64_BOOT_GATE_SV39_ACTIVE
]
expect(check_rv64_boot_gate_transcript(lines)).to_equal("FAIL:duplicate-or-replayed:sv39-active")
```

</details>

#### rejects an unknown canonical receipt token

- rejects an unknown canonical receipt token
   - Expected: check_rv64_boot_gate_transcript(lines) equals `FAIL:unknown-observation:network-probably-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects an unknown canonical receipt token")
val lines = [RV64_BOOT_GATE_RECEIPT_PREFIX + "network-probably-ready"]
expect(check_rv64_boot_gate_transcript(lines)).to_equal("FAIL:unknown-observation:network-probably-ready")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `1f1efdf6081b4dc1e301a08ec010d4ab4f4984cd098a72f2ef13098fd2f8549b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1f1efdf6081b4dc1e301a08ec010d4ab4f4984cd098a72f2ef13098fd2f8549b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1f1efdf6081b4dc1e301a08ec010d4ab4f4984cd098a72f2ef13098fd2f8549b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/rv64_boot_gate_spec.spl
mirror: doc/06_spec/01_unit/os/rv64_boot_gate_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/rv64_boot_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/rv64_boot_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/rv64_boot_gate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/rv64_boot_gate_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the exact ordered lifecycle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/rv64_boot_gate_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the first missing lifecycle observation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/rv64_boot_gate_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a reordered observation and retains that first error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
