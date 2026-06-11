# VexRiscv-SMP Import Specification

> Verifies AC-1: at least one proven RV64 core (VexRiscv-SMP) is imported under src/lib/hardware/opensource_rtl/ with LICENSE and build docs. Tests that the import manifest, port-map API, and .v filename resolution functions return correct values.

<!-- sdn-diagram:id=vexriscv_smp_import_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vexriscv_smp_import_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vexriscv_smp_import_spec -> std
vexriscv_smp_import_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vexriscv_smp_import_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VexRiscv-SMP Import Specification

Verifies AC-1: at least one proven RV64 core (VexRiscv-SMP) is imported under src/lib/hardware/opensource_rtl/ with LICENSE and build docs. Tests that the import manifest, port-map API, and .v filename resolution functions return correct values.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | opensource-riscv-rtl-simpleos |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | REQ-1 |
| Source | `test/01_unit/lib/hardware/opensource_rtl/vexriscv_smp/vexriscv_smp_import_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies AC-1: at least one proven RV64 core (VexRiscv-SMP) is imported
under src/lib/hardware/opensource_rtl/ with LICENSE and build docs.
Tests that the import manifest, port-map API, and .v filename resolution
functions return correct values.

Covers:
- AC-1 (RV64 core imported with license + build docs)

## Scenarios

### VexRiscvSmpPortMap

#### AC-1: single-core port map has axi_data_width 128

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_single_core_config()
expect(cfg.axi_data_width).to_equal(128)
```

</details>

#### AC-1: single-core port map has hart_count 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_single_core_config()
expect(cfg.hart_count).to_equal(1)
```

</details>

#### AC-1: dual-core port map has hart_count 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_dual_core_config()
expect(cfg.hart_count).to_equal(2)
```

</details>

#### AC-1: axi_addr_width is 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_single_core_config()
expect(cfg.axi_addr_width).to_equal(32)
```

</details>

#### AC-1: icache_size_kb is 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_single_core_config()
expect(cfg.icache_size_kb).to_equal(8)
```

</details>

### vexriscv_smp_v_filename

#### AC-1: single-core filename starts with VexRiscvLitexSmpCluster

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_single_core_config()
val name = vexriscv_smp_v_filename(cfg)
expect(name).to_start_with("VexRiscvLitexSmpCluster")
```

</details>

#### AC-1: single-core filename contains Cc1 (1 core)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_single_core_config()
val name = vexriscv_smp_v_filename(cfg)
expect(name).to_contain("Cc1")
```

</details>

#### AC-1: dual-core filename contains Cc2 (2 cores)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_dual_core_config()
val name = vexriscv_smp_v_filename(cfg)
expect(name).to_contain("Cc2")
```

</details>

#### AC-1: filename contains Iw64 (64-bit instruction bus)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_single_core_config()
val name = vexriscv_smp_v_filename(cfg)
expect(name).to_contain("Iw64")
```

</details>

#### AC-1: filename contains Dw64 (64-bit data bus)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_single_core_config()
val name = vexriscv_smp_v_filename(cfg)
expect(name).to_contain("Dw64")
```

</details>

#### AC-1: filename contains Ldw128 (128-bit LiteDRAM interface)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_single_core_config()
val name = vexriscv_smp_v_filename(cfg)
expect(name).to_contain("Ldw128")
```

</details>

#### AC-1: filename ends with .v

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = make_single_core_config()
val name = vexriscv_smp_v_filename(cfg)
expect(name).to_end_with(".v")
```

</details>

### vexriscv_smp_import_path

#### AC-1: import path is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = vexriscv_smp_import_path()
val len = p.length()
expect(len).to_be_greater_than(0)
```

</details>

#### AC-1: import path contains opensource_rtl

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = vexriscv_smp_import_path()
expect(p).to_contain("opensource_rtl")
```

</details>

#### AC-1: import path contains vexriscv_smp

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = vexriscv_smp_import_path()
expect(p).to_contain("vexriscv_smp")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [REQ-1](REQ-1)


</details>
