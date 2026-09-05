# SimpleOS server execution matrix

> Exercises the production evidence rows for ARM64 QEMU, physical UNO Q CPU,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS server execution matrix

Exercises the production evidence rows for ARM64 QEMU, physical UNO Q CPU,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/server/simpleos_server_execution_matrix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises the production evidence rows for ARM64 QEMU, physical UNO Q CPU,
physical UNO Q GPU, Linux CPU comparison, and Linux optional-GPU comparison.
Every live runner must return a provenance-bound
`SimpleOsServerExecutionReceiptV1`. Missing target runners fail explicitly;
source inspection, marker executables, hosted substitutes, and unavailable-row
skips receive no acceptance credit.

The bounded mounted database credential is input only. Its bytes are never a
receipt field and must be redacted from retained commands, transcripts, and logs.

## Scenarios

### SimpleOS server execution matrix

#### should filesystem-launch the ARM64 QEMU server and prove HTTP plus reboot persistence

- should filesystem-launch the ARM64 QEMU server and prove HTTP plus reboot persistence
   - Artifact capture: after_step
- Boot ARM QEMU server executable
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: receipt.mode equals `qemu-arm64-cpu`
- Serve a filesystem document over HTTP
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: expect_http_file(receipt) is true
- Persist and reload a database value
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: expect_db_reboot(receipt) is true
   - Expected: expect_cpu_mode(receipt) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should filesystem-launch the ARM64 QEMU server and prove HTTP plus reboot persistence")
step("Boot ARM QEMU server executable")
val receipt = arm_qemu_server_fixture("qemu-arm64-cpu")
expect(receipt.mode).to_equal("qemu-arm64-cpu")
step("Serve a filesystem document over HTTP")
expect(expect_http_file(receipt)).to_equal(true)
step("Persist and reload a database value")
expect(expect_db_reboot(receipt)).to_equal(true)
expect(expect_cpu_mode(receipt)).to_equal(true)
```

</details>

#### should filesystem-launch the physical UNO Q server in forced CPU-only mode

- should filesystem-launch the physical UNO Q server in forced CPU-only mode
   - Artifact capture: after_step
- Launch UNO Q server executable
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: receipt.mode equals `unoq-cpu`
   - Expected: expect_http_file(receipt) is true
   - Expected: expect_db_reboot(receipt) is true
- Verify UNO Q CPU-only path
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: expect_cpu_mode(receipt) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should filesystem-launch the physical UNO Q server in forced CPU-only mode")
step("Launch UNO Q server executable")
val receipt = uno_q_server_fixture("unoq-cpu")
expect(receipt.mode).to_equal("unoq-cpu")
expect(expect_http_file(receipt)).to_equal(true)
expect(expect_db_reboot(receipt)).to_equal(true)
step("Verify UNO Q CPU-only path")
expect(expect_cpu_mode(receipt)).to_equal(true)
```

</details>

#### should filesystem-launch the physical UNO Q server with verified GPU work

- should filesystem-launch the physical UNO Q server with verified GPU work
   - Artifact capture: after_step
- Launch UNO Q server executable
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: receipt.mode equals `unoq-gpu`
   - Expected: expect_http_file(receipt) is true
   - Expected: expect_db_reboot(receipt) is true
- Verify UNO Q GPU-accelerated path
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: expect_gpu_receipt(receipt) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should filesystem-launch the physical UNO Q server with verified GPU work")
step("Launch UNO Q server executable")
val receipt = uno_q_server_fixture("unoq-gpu")
expect(receipt.mode).to_equal("unoq-gpu")
expect(expect_http_file(receipt)).to_equal(true)
expect(expect_db_reboot(receipt)).to_equal(true)
step("Verify UNO Q GPU-accelerated path")
expect(expect_gpu_receipt(receipt)).to_equal(true)
```

</details>

#### should retain an equivalent Linux CPU comparison row

- should retain an equivalent Linux CPU comparison row
   - Artifact capture: after_step
- Serve a filesystem document over HTTP
   - Artifact capture: after_step
- Persist and reload a database value
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain an equivalent Linux CPU comparison row")
step("Serve a filesystem document over HTTP")
step("Persist and reload a database value")
fail("missing live Linux CPU comparison helper: run equivalent Simple, nginx, PostgreSQL, and SQLite operations with fixed affinity, concurrency, durability, dataset, warmup, samples, p50, p95, throughput, and RSS controls")
```

</details>

#### should retain an optional-GPU Linux comparison without moving mutable server state

- should retain an optional-GPU Linux comparison without moving mutable server state
   - Artifact capture: after_step
- Serve a filesystem document over HTTP
   - Artifact capture: after_step
- Persist and reload a database value
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain an optional-GPU Linux comparison without moving mutable server state")
step("Serve a filesystem document over HTTP")
step("Persist and reload a database value")
fail("missing live Linux optional-GPU comparison helper: prove the exact immutable compute boundary, CUDA submit and validated result, parent-owned socket database and filesystem state, and absence of CUDA loading in the CPU-only row")
```

</details>

<details>
<summary>Advanced: should reject markers substitutions incomplete receipts and GPU fallback</summary>

#### should reject markers substitutions incomplete receipts and GPU fallback

- should reject markers substitutions incomplete receipts and GPU fallback
   - Log capture: after_step
- Boot ARM QEMU server executable
   - Log capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject markers substitutions incomplete receipts and GPU fallback")
step("Boot ARM QEMU server executable")
fail("missing live deliberate-red receipt checker: reject marker apps, host or Linux substitution, stale or incomplete provenance, software-GPU fallback, unowned mutable state, and receiptless results")
```

</details>


</details>

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

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-005`
- `REQ-006`
- `REQ-007`
- `REQ-008`
- `REQ-009`
- `REQ-010`
- `REQ-011`
- `REQ-012`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `067b8f78244ea86b5d066eafc7c8ed93e8636798703283acb13ef7f9d7cc4350`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `067b8f78244ea86b5d066eafc7c8ed93e8636798703283acb13ef7f9d7cc4350`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `067b8f78244ea86b5d066eafc7c8ed93e8636798703283acb13ef7f9d7cc4350`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/server/simpleos_server_execution_matrix_spec.spl
mirror: doc/06_spec/03_system/os/server/simpleos_server_execution_matrix_spec.md (current)
findings: 12 blockers: 1
  narrative=100 structure=70 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/os/server/simpleos_server_execution_matrix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/server/simpleos_server_execution_matrix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/server/simpleos_server_execution_matrix_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 12 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/os/server/simpleos_server_execution_matrix_spec.spl:55:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should filesystem-launch the ARM64 QEMU server and prove HTTP plus reboot persistence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/server/simpleos_server_execution_matrix_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should filesystem-launch the ARM64 QEMU server and prove HTTP plus reboot persistence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/server/simpleos_server_execution_matrix_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should filesystem-launch the physical UNO Q server in forced CPU-only mode' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/server/simpleos_server_execution_matrix_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should filesystem-launch the physical UNO Q server in forced CPU-only mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/server/simpleos_server_execution_matrix_spec.spl:86:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should filesystem-launch the physical UNO Q server with verified GPU work' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/server/simpleos_server_execution_matrix_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should filesystem-launch the physical UNO Q server with verified GPU work' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/server/simpleos_server_execution_matrix_spec.spl:101:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain an equivalent Linux CPU comparison row' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/server/simpleos_server_execution_matrix_spec.spl:112:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain an optional-GPU Linux comparison without moving mutable server state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/server/simpleos_server_execution_matrix_spec.spl:121:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject markers substitutions incomplete receipts and GPU fallback' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
