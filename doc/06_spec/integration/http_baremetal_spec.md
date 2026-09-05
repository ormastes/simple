# HTTP Server on RISC-V Baremetal Specification

> This spec intentionally does not claim HTTP/TLS production success while the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTTP Server on RISC-V Baremetal Specification

This spec intentionally does not claim HTTP/TLS production success while the

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #B6-HTTP-BAREMETAL |
| Category | Infrastructure |
| Status | In Progress |
| Source | `test/integration/http_baremetal_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This spec intentionally does not claim HTTP/TLS production success while the
RISC-V boot path lacks packet RX/TX. The default QEMU scripts remain the real
production HTTP socket gates. Their `--expect-deferred` mode is the current
boundary check: virtio discovery works, packet RX is unavailable, HTTP is
deferred, and the kernel reaches the boot idle loop.

## Scenarios

### HTTP baremetal QEMU gate

#### keeps RV64 default mode as the production HTTP socket gate

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps RV64 default mode as the production HTTP socket gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps RV64 default mode as the production HTTP socket gate")
expect_script_default_mode_remains_http_gate("scripts/qemu_rv64_http_test.shs")
```

</details>

#### keeps RV32 default mode as the production HTTP socket gate

- keeps RV32 default mode as the production HTTP socket gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps RV32 default mode as the production HTTP socket gate")
expect_script_default_mode_remains_http_gate("scripts/qemu_rv32_http_test.shs")
```

</details>

#### documents RV64 deferred mode as the current non-production boundary

- documents RV64 deferred mode as the current non-production boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("documents RV64 deferred mode as the current non-production boundary")
expect_script_has_deferred_boundary("scripts/qemu_rv64_http_test.shs")
```

</details>

#### documents RV32 deferred mode as the current non-production boundary

- documents RV32 deferred mode as the current non-production boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("documents RV32 deferred mode as the current non-production boundary")
expect_script_has_deferred_boundary("scripts/qemu_rv32_http_test.shs")
```

</details>

### HTTP baremetal production blockers

#### records missing packet RX/TX before HTTP can be production-ready

- records missing packet RX/TX before HTTP can be production-ready


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("records missing packet RX/TX before HTTP can be production-ready")
val plan = rt_file_read_text("doc/03_plan/os/riscv/riscv_rtl_simpleos_boot.md")

expect(plan).to_contain("packet RX/TX")
expect(plan).to_contain("QEMU HTTP test cannot yet prove an actual socket response")
expect(plan).to_contain("rt_io_tcp_accept_timeout()")
```

</details>

#### records TLS as blocked rather than production-ready

- records TLS as blocked rather than production-ready


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("records TLS as blocked rather than production-ready")
val plan = rt_file_read_text("doc/03_plan/os/riscv/riscv_rtl_simpleos_boot.md")

expect(plan).to_contain("TLS Baremetal")
expect(plan).to_contain("Blocked, not complete")
expect(plan).to_contain("Tls13AcceptResult.Failed")
```

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `31586512c9253c777470c086ea9f9c028c9d04aff10b9ebb3cab83090b991eb8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `31586512c9253c777470c086ea9f9c028c9d04aff10b9ebb3cab83090b991eb8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `31586512c9253c777470c086ea9f9c028c9d04aff10b9ebb3cab83090b991eb8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/http_baremetal_spec.spl
mirror: doc/06_spec/integration/http_baremetal_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/http_baremetal_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/http_baremetal_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/http_baremetal_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps RV64 default mode as the production HTTP socket gate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/http_baremetal_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps RV32 default mode as the production HTTP socket gate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/http_baremetal_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents RV64 deferred mode as the current non-production boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
