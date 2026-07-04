# sandbox_boot_apply_spec

> expect(embedded_sandbox_section_text_valid(lowering)).to_equal(true)

<!-- sdn-diagram:id=sandbox_boot_apply_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sandbox_boot_apply_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sandbox_boot_apply_spec -> std
sandbox_boot_apply_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sandbox_boot_apply_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sandbox_boot_apply_spec

expect(embedded_sandbox_section_text_valid(lowering)).to_equal(true)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/security/sandbox_boot_apply_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

expect(embedded_sandbox_section_text_valid(lowering)).to_equal(true)
        expect(embedded_sandbox_lowering_sdn_from_section(4096, 8192, lowering)).to_equal(lowering)

    it "maps lowered region size and permissions to ARM MPU RASR bits":
        expect(arm_mpu_region_size_encoding(4096)).to_equal(11)
        expect(arm_mpu_access_permission_bits("rw")).to_equal(3 << 24)
        expect((arm_mpu_rasr_value(4096, "rw") & ARM_MPU_RASR_XN) != 0).to_equal(true)
        expect((arm_mpu_rasr_value(4096, "rx") & ARM_MPU_RASR_XN) == 0).to_equal(true)

    it "builds concrete ARM MPU MMIO writes from sandbox lowering":
        val lowering = """
sandbox_lowering:
  pmp_region|2147483648|4096|rw|locked

## Scenarios

### sandbox boot apply metadata and ARM MPU planning

#### fails closed for missing embedded sandbox section bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(embedded_sandbox_section_bounds_valid(0, 4096)).to_equal(false)
expect(embedded_sandbox_lowering_sdn_from_section(4096, 4096, "sandbox_lowering:")).to_equal("")
expect(embedded_sandbox_lowering_sdn_from_raw_bounds(0, 0)).to_equal("")
```

</details>

#### accepts bounded generated sandbox lowering section text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lowering = """
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
