# nvme_firmware_remaining_gates_spec

> This specification prepares the checks that become runnable after a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvme_firmware_remaining_gates_spec

This specification prepares the checks that become runnable after a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/nvme_firmware/nvme_firmware_remaining_gates_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations


This specification prepares the checks that become runnable after a
source-matched pure-Simple runtime is deployed. It verifies explicit current
and requested target profiles, rejects incomplete physical-board evidence, and
keeps UNO Q evidence supplementary. It does not claim REQ-012, NFR-011, or
physical target availability from profile/package evidence.

## Scenarios

### NVMe firmware remaining gates

#### should retain simulator and OpenSSD target profiles

- Verify: should retain simulator and OpenSSD target profiles
- Inspect the current target-neutral firmware configuration


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-012
step("Verify: should retain simulator and OpenSSD target profiles")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Inspect the current target-neutral firmware configuration")
val source = file_read_text(TARGETS)
expect(source).to_contain("TARGET_SIMPLE_SIM")
expect(source).to_contain("TARGET_OPENSSD_2CH8WAY")
expect(source).to_contain("TARGET_OPENSSD_8CH8WAY")
expect(source).to_contain("TARGET_RV32_QEMU_RAM_NAND")
expect(source).to_contain("TARGET_RV32_KV260_AXI_RAM_NAND")
expect(source).to_contain("TARGET_INVALID")
expect(source).to_contain("fn nvme_fw_target_config")
expect(source).to_contain("invalid_target_config()")
expect(source).to_contain("target: unknown fails closed")
expect(source).to_contain("available: false")
```

</details>

#### should track QEMU and FPGA profiles without fabricating support

- Verify: should track QEMU and FPGA profiles without fabricating support
- Inspect the selected multi-target feature request


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-012
step("Verify: should track QEMU and FPGA profiles without fabricating support")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Inspect the selected multi-target feature request")
val requests = file_read_text(REQUESTS)
expect(requests).to_contain("QEMU/FEMU")
expect(requests).to_contain("KV260/FPGA")
expect(requests).to_contain("fail closed")
expect(requests).to_contain("they do not fork the NVMe command, FTL, or recovery core")
```

</details>

#### should reject incomplete board evidence and postpone unavailable environments

- Verify: should reject incomplete board evidence and postpone unavailable environments
- Run the remaining-gate contract self-test
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-012
step("Verify: should reject incomplete board evidence and postpone unavailable environments")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Run the remaining-gate contract self-test")
val (out, err, code) = _run("sh " + GATE + " --self-test")
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(err).to_equal("")
expect(out).to_contain("TARGET simple-sim PROFILE_PRESENT")
expect(out).to_contain("TARGET openssd-2ch8way PROFILE_PRESENT H2_POSTPONED")
expect(out).to_contain("TARGET openssd-8ch8way PROFILE_PRESENT H2_POSTPONED")
expect(out).to_contain("COSMOS_PACKAGE_PROVENANCE_PASS source=clean board=bound tools=clang,lld,bootgen")
expect(out).to_contain("REJECTION missing-bt PASS")
expect(out).to_contain("REJECTION tampered-log PASS")
expect(out).to_contain("REJECTION path-traversal PASS")
expect(out).to_contain("REJECTION duplicate-field PASS")
expect(out).to_contain("REJECTION same-reviewer PASS")
expect(out).to_contain("REJECTION package-source-mismatch PASS")
expect(out).to_contain("STATUS: PASS nvme-firmware-remaining-gates self-test")
expect(out).to_contain("STATUS: POSTPONED uno-q-supplementary environment-unavailable")
expect(out).to_contain("STATUS: POSTPONED cosmos-board BT-001..BT-006")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `36c4d3e4520fabfb6dfca422e175e8c9a807da0f417aa0b0a63bb89807512aa8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `36c4d3e4520fabfb6dfca422e175e8c9a807da0f417aa0b0a63bb89807512aa8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `36c4d3e4520fabfb6dfca422e175e8c9a807da0f417aa0b0a63bb89807512aa8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/nvme_firmware/nvme_firmware_remaining_gates_spec.spl
mirror: doc/06_spec/03_system/app/nvme_firmware/nvme_firmware_remaining_gates_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/nvme_firmware/nvme_firmware_remaining_gates_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/nvme_firmware/nvme_firmware_remaining_gates_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/nvme_firmware/nvme_firmware_remaining_gates_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/nvme_firmware/nvme_firmware_remaining_gates_spec.spl:34:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain simulator and OpenSSD target profiles' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/nvme_firmware_remaining_gates_spec.spl:51:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should track QEMU and FPGA profiles without fabricating support' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/nvme_firmware_remaining_gates_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject incomplete board evidence and postpone unavailable environments' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
