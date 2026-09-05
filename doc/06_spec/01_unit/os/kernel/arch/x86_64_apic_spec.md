# x86_64 Local APIC ICR Encoding Specification

> <details>

<!-- sdn-diagram:id=x86_64_apic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_64_apic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_64_apic_spec -> std
x86_64_apic_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_64_apic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x86_64 Local APIC ICR Encoding Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/x86_64_apic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### x86_64 APIC ICR encoding

#### encodes physical destination APIC id in ICR high

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(apic_icr_high_for_apic_id(0x12u32)).to_equal(0x12000000u32)
expect(apic_icr_high_for_apic_id(0x123u32)).to_equal(0x23000000u32)
```

</details>

#### encodes fixed-vector IPIs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(apic_icr_low_fixed(0x41u8)).to_equal(0x41u32)
```

</details>

#### encodes INIT assert for AP startup

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(apic_icr_low_init()).to_equal(0xC500u32)
```

</details>

#### encodes Startup IPI vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(apic_icr_low_sipi(0x08u8)).to_equal(0x608u32)
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
