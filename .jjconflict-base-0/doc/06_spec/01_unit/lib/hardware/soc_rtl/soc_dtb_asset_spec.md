# Soc Dtb Asset Specification

> Tests covering shared full Linux DTB asset.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Soc Dtb Asset Specification

## Scenarios

### shared full Linux DTB asset

#### has aligned, bounded FDT header and structure blocks

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has aligned, bounded FDT header and structure blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has aligned, bounded FDT header and structure blocks")
expect(fdt_structure_is_well_formed(soc_rv32_linux_dtb(0, 0))).to_be(true)
expect(fdt_structure_is_well_formed(soc_rv64_linux_dtb(0, 0))).to_be(true)
```

</details>

#### describes the shared topology with truthful arch and interrupt cells

- describes the shared topology with truthful arch and interrupt cells


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes the shared topology with truthful arch and interrupt cells")
val rv32 = soc_rv32_linux_dtb(0, 0)
val rv64 = soc_rv64_linux_dtb(0, 0)
expect(blob_contains_ascii(rv32, "cpu@0")).to_be(true)
expect(blob_contains_ascii(rv32, "interrupt-controller")).to_be(true)
expect(blob_contains_ascii(rv32, "memory@80000000")).to_be(true)
expect(blob_contains_ascii(rv32, "chosen")).to_be(true)
expect(blob_contains_ascii(rv32, "uart@10000000")).to_be(true)
expect(blob_contains_ascii(rv32, "clint@2000000")).to_be(true)
expect(blob_contains_ascii(rv32, "plic@c000000")).to_be(true)
expect(blob_contains_ascii(rv32, "rv32imac_zicsr_zifencei")).to_be(true)
expect(blob_contains_ascii(rv32, "riscv,sv32")).to_be(true)
expect(blob_contains_ascii(rv64, "rv64imac_zicsr_zifencei_svade")).to_be(true)
expect(blob_contains_ascii(rv64, "riscv,sv39")).to_be(true)
expect(blob_contains_cells(rv32, [0, 0x80000000, 0, 0x10000000])).to_be(true)
expect(blob_contains_cells(rv32, [0, 0x0C000000, 0, 0x04000000])).to_be(true)
expect(blob_contains_cells(rv64, [0, 0x0C000000, 0, 0x00400000])).to_be(true)
expect(blob_contains_cells(rv32, [1, 3, 1, 7])).to_be(true)
expect(blob_contains_cells(rv32, [1, 11, 1, 9])).to_be(true)
expect(blob_contains_ascii(rv32, "phandle")).to_be(true)
expect(blob_contains_ascii(rv32, "interrupt-parent")).to_be(true)
expect(blob_contains_ascii(rv32, "interrupts-extended")).to_be(true)
expect(fdt_node_property_cells_equal(rv32,
    "interrupt-controller", "phandle", [1])).to_be(true)
expect(fdt_node_property_cells_equal(rv32,
    "plic@c000000", "phandle", [2])).to_be(true)
expect(fdt_node_property_cells_equal(rv32,
    "uart@10000000", "interrupt-parent", [2])).to_be(true)
expect(fdt_node_property_cells_equal(rv32,
    "uart@10000000", "interrupts", [10])).to_be(true)
expect(fdt_node_property_cells_equal(rv32,
    "clint@2000000", "interrupts-extended", [1, 3, 1, 7])).to_be(true)
expect(fdt_node_property_cells_equal(rv32,
    "plic@c000000", "interrupts-extended", [1, 11, 1, 9])).to_be(true)
```

</details>

#### reserves the DTB and emits initrd cells only when present

- reserves the DTB and emits initrd cells only when present


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reserves the DTB and emits initrd cells only when present")
val absent = soc_rv32_linux_dtb_for_ram_initrd(0x10000000, 0, 0)
val present32 = soc_rv32_linux_dtb_for_ram_initrd(
    0x10000000, 0x84000000, 0x84800000)
val present64 = soc_rv64_linux_dtb_for_ram_initrd(
    0x10000000, 0x84000000, 0x84800000)
val overlaps_dtb = soc_rv64_linux_dtb_for_ram_initrd(
    0x10000000, 0x87FFF000, 0x88001000)
val after_dtb = soc_rv64_linux_dtb_for_ram_initrd(
    0x10000000, 0x88010000, 0x88800000)
expect(blob_contains_ascii(absent, "reserved-memory")).to_be(true)
expect(blob_contains_ascii(absent, "dtb@88000000")).to_be(true)
expect(blob_contains_ascii(absent, "no-map")).to_be(true)
expect(blob_contains_cells(absent, [0, 0x88000000, 0, 0x10000])).to_be(true)
expect(blob_contains_ascii(absent, "linux,initrd-start")).to_be(false)
expect(blob_contains_ascii(present32, "linux,initrd-start")).to_be(true)
expect(blob_contains_ascii(present32, "linux,initrd-end")).to_be(true)
expect(blob_contains_cells(present32, [0, 0x84000000])).to_be(true)
expect(blob_contains_cells(present64, [0, 0x84800000])).to_be(true)
expect(blob_contains_ascii(overlaps_dtb, "linux,initrd-start")).to_be(false)
expect(blob_contains_ascii(overlaps_dtb, "linux,initrd-end")).to_be(false)
expect(blob_contains_ascii(after_dtb, "linux,initrd-start")).to_be(true)
```

</details>

#### passes production initrd bounds through scalar DTB metadata

- passes production initrd bounds through scalar DTB metadata
   - Expected: rv32.dtb_initrd_start equals `0x84000000`
   - Expected: rv32.dtb_initrd_end equals `0x84800000`
   - Expected: rv64.dtb_initrd_start equals `0x84000000`
   - Expected: rv64.dtb_initrd_end equals `0x84800000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes production initrd bounds through scalar DTB metadata")
val rv32 = soc_protected32_create_with_initrd(
    0, 0x84000000, 0x84800000)
val rv64 = soc_top_64_protected_init_with_initrd(
    0x84000000, 0x84800000)
expect(rv32.dtb_initrd_start).to_equal(0x84000000)
expect(rv32.dtb_initrd_end).to_equal(0x84800000)
expect(rv64.dtb_initrd_start).to_equal(0x84000000)
expect(rv64.dtb_initrd_end).to_equal(0x84800000)
```

</details>

#### preloads a complete read-only FDT in both SoCs

- preloads a complete read-only FDT in both SoCs
   - Expected: dtb_total_size(rv32_blob) equals `rv32_blob.len().to_u64()`
   - Expected: dtb_total_size(rv64_blob) equals `rv64_blob.len().to_u64()`
   - Expected: rv32.dtb_size equals `0x10000`
   - Expected: rv64.dtb_size equals `0x10000`
   - Expected: rv32.dram_size equals `0x10000000`
   - Expected: rv64.ram.size equals `0x10000000`
   - Expected: soc_protected32_read(rv32, 0x88000000) equals `0xEDFE0DD0`
   - Expected: soc64_mem_read(rv64_written, 0x88000000, 4) equals `0xEDFE0DD0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preloads a complete read-only FDT in both SoCs")
val rv32_blob = soc_rv32_linux_dtb(0, 0)
val rv64_blob = soc_rv64_linux_dtb(0, 0)
val rv32 = soc_protected32_sim_preload_dtb(soc_protected32_create(0))
val rv64 = soc_top_64_sim_preload_dtb(soc_top_64_protected_init())
val rv64_written = soc64_mem_write(rv64, 0x88000000, 4, 0)

expect(dtb_total_size(rv32_blob)).to_equal(rv32_blob.len().to_u64())
expect(dtb_total_size(rv64_blob)).to_equal(rv64_blob.len().to_u64())
expect(rv32.dtb_size).to_equal(0x10000)
expect(rv64.dtb_size).to_equal(0x10000)
expect(rv32_blob.len()).to_be_less_than(rv32.dtb_size as i64)
expect(rv64_blob.len()).to_be_less_than(rv64.dtb_size)
expect(rv32.dram_size).to_equal(0x10000000)
expect(rv64.ram.size).to_equal(0x10000000)
expect(soc_protected32_read(rv32, 0x88000000)).to_equal(0xEDFE0DD0)
expect(soc64_mem_read(rv64_written, 0x88000000, 4)).to_equal(0xEDFE0DD0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/hardware/soc_rtl/soc_dtb_asset_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering shared full Linux DTB asset.
- shared full Linux DTB asset

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `b39211327a75f7fe944233ab4dc3098a553bcd426be1d1818f215268eba0d8b2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b39211327a75f7fe944233ab4dc3098a553bcd426be1d1818f215268eba0d8b2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b39211327a75f7fe944233ab4dc3098a553bcd426be1d1818f215268eba0d8b2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/hardware/soc_rtl/soc_dtb_asset_spec.spl
mirror: doc/06_spec/01_unit/lib/hardware/soc_rtl/soc_dtb_asset_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/hardware/soc_rtl/soc_dtb_asset_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/hardware/soc_rtl/soc_dtb_asset_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/hardware/soc_rtl/soc_dtb_asset_spec.spl:162:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has aligned, bounded FDT header and structure blocks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/soc_rtl/soc_dtb_asset_spec.spl:168:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'describes the shared topology with truthful arch and interrupt cells' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/soc_rtl/soc_dtb_asset_spec.spl:205:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reserves the DTB and emits initrd cells only when present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
