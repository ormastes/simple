# nvme_units_spec

> NVMe firmware + emulator unit self-tests (per-layer leaf coverage).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvme_units_spec

NVMe firmware + emulator unit self-tests (per-layer leaf coverage).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NVME-UNIT-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md |
| Design | N/A |
| Research | doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md |
| Source | `test/01_unit/app/nvme_firmware/nvme_units_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

NVMe firmware + emulator unit self-tests (per-layer leaf coverage).

The unit tier exercises the pure-Simple firmware and emulator self-test
aggregators that live under examples/09_embedded/simpleos_nvme_fw/. Those modules
cannot be bare-imported from test/ (cross-example import is unsupported), so the
tier drives each aggregator through the real CLI (`bin/simple run`) as a
subprocess and asserts the operator-visible per-layer PASS evidence — exactly
what the generated manual shows. Run:
`bin/simple test test/01_unit/app/nvme_firmware/nvme_units_spec.spl`.

## Scenarios

### NVMe firmware unit self-tests (per-layer)

#### passes every per-layer firmware self-test (FIL, FTL, HIL, NVMe controller)

- passes every per-layer firmware self-test (FIL, FTL, HIL, NVMe controller)
- Run the firmware self-test aggregator through the CLI
   - Expected: code equals `0`
- The FIL (flash interface) layer reports its self-test section
- The FTL (translation) layer reports its self-test section
- The HIL (host interface) layer reports its self-test section
- The NVMe controller (admin + multi IO queue) reports its self-test section
- The aggregator reports overall firmware PASS


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("passes every per-layer firmware self-test (FIL, FTL, HIL, NVMe controller)")
step("Run the firmware self-test aggregator through the CLI")
val (out, err, code) = _run(FW + "/test_fw.spl")
expect(code).to_equal(0)

step("The FIL (flash interface) layer reports its self-test section")
expect(out).to_contain("FIL (flash interface)")

step("The FTL (translation) layer reports its self-test section")
expect(out).to_contain("FTL (translation)")

step("The HIL (host interface) layer reports its self-test section")
expect(out).to_contain("HIL (host interface)")

step("The NVMe controller (admin + multi IO queue) reports its self-test section")
expect(out).to_contain("NVMe controller (admin + multi IO queue)")

step("The aggregator reports overall firmware PASS")
expect(out).to_contain("ALL FIRMWARE SELF-TESTS PASS")
```

</details>

### NVMe emulator unit self-tests

#### passes every emulator module self-test (NAND, memcpy, FTL, device)

- passes every emulator module self-test (NAND, memcpy, FTL, device)
- Run the emulator self-test aggregator through the CLI
   - Expected: code equals `0`
- The aggregator reports overall emulator PASS


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("passes every emulator module self-test (NAND, memcpy, FTL, device)")
step("Run the emulator self-test aggregator through the CLI")
val (out, err, code) = _run(EMU + "/test_emu.spl")
expect(code).to_equal(0)

step("The aggregator reports overall emulator PASS")
expect(out).to_contain("ALL EMU SELFTESTS PASS")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/hardware/nvme_fw_baremetal_parallel_agent_plan.md`
- **Research:** `doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `16f4419ea4b7b2853d22f5b5beb0b59c27b815b45ef710924d0833a829266713`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `16f4419ea4b7b2853d22f5b5beb0b59c27b815b45ef710924d0833a829266713`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `16f4419ea4b7b2853d22f5b5beb0b59c27b815b45ef710924d0833a829266713`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/app/nvme_firmware/nvme_units_spec.spl
mirror: doc/06_spec/01_unit/app/nvme_firmware/nvme_units_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/nvme_firmware/nvme_units_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/nvme_firmware/nvme_units_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/nvme_firmware/nvme_units_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/nvme_firmware/nvme_units_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes every per-layer firmware self-test (FIL, FTL, HIL, NVMe controller)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/nvme_firmware/nvme_units_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes every emulator module self-test (NAND, memcpy, FTL, device)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
