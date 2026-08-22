# nvme_nand_capture_spec

> Verifies the nvme nand capture behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvme_nand_capture_spec

Verifies the nvme nand capture behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NVME-NAND-CAP-001 |
| Category | Hardware |
| Difficulty | 4/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/hardware/nvme_fw_emulated_nand_plan.md |
| Design | N/A |
| Research | doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md |
| Source | `test/03_system/app/nvme_firmware/nvme_nand_capture_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the nvme nand capture behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### NVMe NAND emulation: data change captured on write and read

#### captures the emulated NAND words changing from zeros to data and reading back intact

- Verify: captures the emulated NAND words changing from zeros to data and reading back intact
- Run the NAND data-change capture demo through the CLI
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
- Before the write, the target NAND page words are all zero
- After the write, the same NAND page words hold the written data
   - Expected: capture_bit_table("nand_page0_after_write", [161, 178, 195, 212], "bits16", ["w0", "w1", "w2", "w3"]) is true
- Reading the LBA back returns exactly the written NAND words
- The demo confirms the NAND data change was captured
- The end-to-end capture scenario reports overall PASS


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-nvme_nand_capture
# @req: REQ-APP-NVME_FIRMWARE_NVME_NAND_CAPT-001
step("Verify: captures the emulated NAND words changing from zeros to data and reading back intact")
step("Run the NAND data-change capture demo through the CLI")
val (out, err, code) = run_nand_write_read_demo()
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario

step("Before the write, the target NAND page words are all zero")
expect(out).to_contain("NAND-BEFORE ppn=0 words=0,0,0,0")

step("After the write, the same NAND page words hold the written data")
expect(out).to_contain("NAND-AFTER ppn=0 words=161,178,195,212")
expect(capture_bit_table("nand_page0_after_write", [161, 178, 195, 212], "bits16", ["w0", "w1", "w2", "w3"])).to_equal(true)
expect(capture_text("nand_page0_after_write")).to_contain("bytes: 0xa1 0xb2 0xc3 0xd4")

step("Reading the LBA back returns exactly the written NAND words")
expect(out).to_contain("NAND-READBACK lba=5 words=161,178,195,212")

step("The demo confirms the NAND data change was captured")
expect(out).to_contain("NAND DATA CHANGE CAPTURED")

step("The end-to-end capture scenario reports overall PASS")
expect(out).to_contain("NVME NAND CAPTURE PASS")
_expect_no_fail_marker(out, "NAND data-change capture demo")
```

</details>

### NVMe NAND emulation: FTL block migration captured

#### captures an LBA migrating across physical NAND blocks with data preserved and victim erased

- Verify: captures an LBA migrating across physical NAND blocks with data preserved and victim erased
- Run the NAND FTL block-migration capture demo through the CLI
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
- Before migration, the LBA lives in its original physical NAND block (source phase)
   - Expected: capture_bit_table("ftl_lba100_before_migration", [171], "bits8", ["nand_block"]) is true
- After migration, the LBA has moved to a different physical NAND block (destination phase)
- The demo confirms the FTL block migration was captured
- The end-to-end migration scenario reports overall PASS


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-nvme_nand_capture
# @req: REQ-APP-NVME_FIRMWARE_NVME_NAND_CAPT-001
step("Verify: captures an LBA migrating across physical NAND blocks with data preserved and victim erased")
step("Run the NAND FTL block-migration capture demo through the CLI")
val (out, err, code) = run_ftl_migration_demo()
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario

step("Before migration, the LBA lives in its original physical NAND block (source phase)")
expect(out).to_contain("MIGRATE-BEFORE lba=100 block=0 nand=171")
expect(capture_bit_table("ftl_lba100_before_migration", [171], "bits8", ["nand_block"])).to_equal(true)
expect(capture_text("ftl_lba100_before_migration")).to_contain("bytes: 0xab")

step("After migration, the LBA has moved to a different physical NAND block (destination phase)")
expect(out).to_contain("MIGRATE-AFTER lba=100 block=")

step("The demo confirms the FTL block migration was captured")
expect(out).to_contain("NAND FTL BLOCK MIGRATION CAPTURED")

step("The end-to-end migration scenario reports overall PASS")
expect(out).to_contain("NAND MIGRATION CAPTURE PASS")
_expect_no_fail_marker(out, "NAND migration capture demo")
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

- **Plan:** `doc/03_plan/hardware/nvme_fw_emulated_nand_plan.md`
- **Research:** `doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9dfbebaf6caf3457defb312e47707a24d91c659353abde51014c564b9a7d1b1d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9dfbebaf6caf3457defb312e47707a24d91c659353abde51014c564b9a7d1b1d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9dfbebaf6caf3457defb312e47707a24d91c659353abde51014c564b9a7d1b1d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/nvme_firmware/nvme_nand_capture_spec.spl
mirror: doc/06_spec/03_system/app/nvme_firmware/nvme_nand_capture_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/nvme_firmware/nvme_nand_capture_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/nvme_firmware/nvme_nand_capture_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/03_system/app/nvme_firmware/nvme_nand_capture_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/nvme_firmware/nvme_nand_capture_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
