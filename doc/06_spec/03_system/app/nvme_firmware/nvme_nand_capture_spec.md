# nvme_nand_capture_spec

> NVMe NAND data-change capture — emulated NAND write/read + FTL block migration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvme_nand_capture_spec

NVMe NAND data-change capture — emulated NAND write/read + FTL block migration.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

NVMe NAND data-change capture — emulated NAND write/read + FTL block migration.

The pure-Simple NVMe firmware emulator tracks NAND state as ONFI-style page
words (four `u32` words per page, matching the ONFI NAND addressing the real
controller uses). Two properties must hold for a host to trust the device:

- **Write/read fidelity.** A host write drives a page's ONFI words from the
  erased all-zero state to the written pattern, and a read of that LBA must
  return exactly those words back — proving the data change is captured
  end-to-end at the NAND level, not just acknowledged.
- **FTL block migration.** The Flash Translation Layer relocates a logical
  block (LBA) across two physical-block phases — the **source phase** (the
  block it lived in before migration) and the **destination phase** (the
  block it lives in after) — while preserving the stored data and erasing the
  vacated victim block.

The capture demos live under `examples/` and cannot be bare-imported from
`test/` (cross-example import is unsupported), so this scenario drives them
through the real CLI (`bin/simple run`) as subprocesses and asserts the
operator-visible NAND-level evidence — exactly what the generated manual
shows. Run:
`bin/simple test test/03_system/app/nvme_firmware/nvme_nand_capture_spec.spl`.

## Scenarios

### NVMe NAND emulation: data change captured on write and read

#### captures the emulated NAND words changing from zeros to data and reading back intact

- captures the emulated NAND words changing from zeros to data and reading back intact
- Run the NAND data-change capture demo through the CLI
   - Expected: code equals `0`
- Before the write, the target NAND page words are all zero
- After the write, the same NAND page words hold the written data
   - Expected: capture_bit_table("nand_page0_after_write", [161, 178, 195, 212], "bits16", ["w0", "w1", "w2", "w3"]) is true
- Reading the LBA back returns exactly the written NAND words
- The demo confirms the NAND data change was captured
- The end-to-end capture scenario reports overall PASS


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("captures the emulated NAND words changing from zeros to data and reading back intact")
step("Run the NAND data-change capture demo through the CLI")
val (out, err, code) = run_nand_write_read_demo()
expect(code).to_equal(0)

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

- captures an LBA migrating across physical NAND blocks with data preserved and victim erased
- Run the NAND FTL block-migration capture demo through the CLI
   - Expected: code equals `0`
- Before migration, the LBA lives in its original physical NAND block (source phase)
   - Expected: capture_bit_table("ftl_lba100_before_migration", [171], "bits8", ["nand_block"]) is true
- After migration, the LBA has moved to a different physical NAND block (destination phase)
- The demo confirms the FTL block migration was captured
- The end-to-end migration scenario reports overall PASS


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("captures an LBA migrating across physical NAND blocks with data preserved and victim erased")
step("Run the NAND FTL block-migration capture demo through the CLI")
val (out, err, code) = run_ftl_migration_demo()
expect(code).to_equal(0)

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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-nvme_nand_capture`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5fe48894152b121c61c87d105ad11489256e21094086c03cf269f0404e8d5b10`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5fe48894152b121c61c87d105ad11489256e21094086c03cf269f0404e8d5b10`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5fe48894152b121c61c87d105ad11489256e21094086c03cf269f0404e8d5b10`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/nvme_firmware/nvme_nand_capture_spec.spl
mirror: doc/06_spec/03_system/app/nvme_firmware/nvme_nand_capture_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/03_system/app/nvme_firmware/nvme_nand_capture_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/nvme_firmware/nvme_nand_capture_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/nvme_firmware/nvme_nand_capture_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/nvme_firmware/nvme_nand_capture_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
<!-- sspec-maintain:scorecard:end -->
