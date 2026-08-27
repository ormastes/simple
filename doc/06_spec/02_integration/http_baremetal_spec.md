# HTTP Server on RISC-V Baremetal Specification

> This spec distinguishes the current RV64 HTTP-only live gate from full

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTTP Server on RISC-V Baremetal Specification

This spec distinguishes the current RV64 HTTP-only live gate from full

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #B6-HTTP-BAREMETAL |
| Category | Infrastructure |
| Status | HTTP-only RV64 live gate passing; HTTPS/TLS still blocked |
| Source | `test/02_integration/http_baremetal_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This spec distinguishes the current RV64 HTTP-only live gate from full
HTTP+HTTPS production readiness. RV64 QEMU now proves packet TX/RX, a boot-local
HTTP response, and optional display/storage service markers. TLS remains
fail-closed until RISC-V has production entropy. Deferred mode stays available
only as a regression boundary for older packet-unavailable images.

## Scenarios

### HTTP baremetal QEMU gate

#### keeps RV64 default mode as the full HTTP plus HTTPS production gate

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps RV64 default mode as the full HTTP plus HTTPS production gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps RV64 default mode as the full HTTP plus HTTPS production gate")
expect_script_default_mode_remains_http_gate("scripts/qemu/qemu_rv64_http_test.shs")
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
expect_script_default_mode_remains_http_gate("scripts/qemu/qemu_rv32_http_test.shs")
```

</details>

#### documents RV64 HTTP-only mode as the current live QEMU boundary

- documents RV64 HTTP-only mode as the current live QEMU boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("documents RV64 HTTP-only mode as the current live QEMU boundary")
expect_script_has_http_only_boundary("scripts/qemu/qemu_rv64_http_test.shs")
```

</details>

#### keeps RV64 deferred mode as a packet-unavailable regression boundary

- keeps RV64 deferred mode as a packet-unavailable regression boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps RV64 deferred mode as a packet-unavailable regression boundary")
expect_script_has_deferred_boundary("scripts/qemu/qemu_rv64_http_test.shs")
expect(rt_file_read_text("scripts/qemu/qemu_rv64_http_test.shs")).to_contain("Network packet RX unavailable")
```

</details>

#### documents RV32 deferred mode as the current non-production boundary

- documents RV32 deferred mode as the current non-production boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("documents RV32 deferred mode as the current non-production boundary")
expect_script_has_deferred_boundary("scripts/qemu/qemu_rv32_http_test.shs")
expect(rt_file_read_text("scripts/qemu/qemu_rv32_http_test.shs")).to_contain("Network packet TX unavailable")
```

</details>

### HTTP baremetal production blockers

#### records RV64 packet RX/TX and HTTP-only QEMU smoke as prebuilt-only evidence until source rebuild passes

- records RV64 packet RX/TX and HTTP-only QEMU smoke as prebuilt-only evidence until source rebuild passes


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("records RV64 packet RX/TX and HTTP-only QEMU smoke as prebuilt-only evidence until source rebuild passes")
val plan = rt_file_read_text("doc/03_plan/os/riscv/riscv_rtl_simpleos_boot.md")

expect(plan).to_contain("HTTP-only prebuilt gate passing; current-source QEMU blocked")
expect(plan).to_contain("packet RX/TX through the boot-local")
expect(plan).to_contain("--expect-http-only")
expect(plan).to_contain("Storage service ready")
expect(plan).to_contain("NVFS root superblock ready")
expect(plan).to_contain("Do not treat the")
expect(plan).to_contain("passing prebuilt ELF smoke as current-source rebuild evidence")
```

</details>

#### records TLS as blocked rather than production-ready

- records TLS as blocked rather than production-ready


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("records TLS as blocked rather than production-ready")
val plan = rt_file_read_text("doc/03_plan/os/riscv/riscv_rtl_simpleos_boot.md")

expect(plan).to_contain("TLS Baremetal")
expect(plan).to_contain("Blocked, not complete")
expect(plan).to_contain("Tls13AcceptResult.Accepted")
expect(plan).to_contain("placeholder_entropy")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `756d087eed10c9fa9616c971c3cfcbf3a02d2cee769ba9d201eb2d8bca0b1bd8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `756d087eed10c9fa9616c971c3cfcbf3a02d2cee769ba9d201eb2d8bca0b1bd8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `756d087eed10c9fa9616c971c3cfcbf3a02d2cee769ba9d201eb2d8bca0b1bd8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/http_baremetal_spec.spl
mirror: doc/06_spec/02_integration/http_baremetal_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/http_baremetal_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/http_baremetal_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/http_baremetal_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps RV64 default mode as the full HTTP plus HTTPS production gate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/http_baremetal_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps RV32 default mode as the production HTTP socket gate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/http_baremetal_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents RV64 HTTP-only mode as the current live QEMU boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
