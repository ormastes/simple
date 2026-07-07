# Vhdl Source Map Debug Specification

> <details>

<!-- sdn-diagram:id=vhdl_source_map_debug_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_source_map_debug_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_source_map_debug_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_source_map_debug_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Source Map Debug Specification

## Scenarios

### VHDL source-map HWIR debug metadata

#### explains a VHDL line through HWIR and Simple source

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rtl_explain_vhdl_line_from_map(sample_map(), 8)
check(result.found)
expect result.hwir_id == "port:a:8"
expect result.signal_name == "a"
expect result.source_line == 2
check(result.to_text().contains("width_narrowing"))
```

</details>

#### returns a missing explanation for unmapped lines

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rtl_explain_vhdl_line_from_map(sample_map(), 42)
check(not result.found)
check(result.to_text().contains("no RTL source-map entry"))
```

</details>

#### renders waveform groups from source-map ports

- expect groups len
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val groups = rtl_waveform_groups_from_map(sample_map())
expect groups.len() == 1
val gtkw = rtl_render_gtkw_from_groups(groups)
check(gtkw.contains("[group] ports"))
check(gtkw.contains("a"))
```

</details>

#### renders first divergence reports

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = rtl_first_divergence_report(12, "0x1000", "0x13", "x1 expected 1 got 0", "", "", "demo.spl:2", "uut.debug_pc", "wave.gtkw")
check(report.contains("First RTL Divergence"))
check(report.contains("uut.debug_pc"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/vhdl_source_map_debug_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- VHDL source-map HWIR debug metadata

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
