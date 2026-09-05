# Zzz Osmain Compile Specification

> <details>

<!-- sdn-diagram:id=zzz_osmain_compile_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zzz_osmain_compile_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zzz_osmain_compile_spec -> std
zzz_osmain_compile_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zzz_osmain_compile_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zzz Osmain Compile Specification

## Scenarios

### os_main compiles

#### module typechecks

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/boot/zzz_osmain_compile_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- os_main compiles

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
