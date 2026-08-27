# Trace32 Wrapper Specification

> <details>

<!-- sdn-diagram:id=trace32_wrapper_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=trace32_wrapper_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

trace32_wrapper_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=trace32_wrapper_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Trace32 Wrapper Specification

## Scenarios

### Trace32 wrapper portable smoke

#### records trace32 backend names

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val native_backend = "trace32"
val gdb_backend = "trace32-gdb"
expect(native_backend).to_equal("trace32")
expect(gdb_backend).to_contain("gdb")
```

</details>

#### records native feature names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = ["Halt", "TraceCapture", "CoverageCollect"]
expect(features.len()).to_equal(3)
expect(features[1]).to_equal("TraceCapture")
```

</details>

#### records default adapter settings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_arch = "arm"
val timeout_ms = 30000
expect(default_arch).to_equal("arm")
expect(timeout_ms).to_equal(30000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/t32_tools/trace32_wrapper_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Trace32 wrapper portable smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
