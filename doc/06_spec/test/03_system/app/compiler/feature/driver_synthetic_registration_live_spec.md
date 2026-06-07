# Driver Synthetic Registration Live Specification

> 1. delete if exists

<!-- sdn-diagram:id=driver_synthetic_registration_live_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=driver_synthetic_registration_live_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

driver_synthetic_registration_live_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=driver_synthetic_registration_live_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Synthetic Registration Live Specification

## Scenarios

### FR-DRIVER-0001 live synthetic registration

#### executes register_static_driver for a stub-only @driver ops function

1. delete if exists
   - Expected: rt_file_write_text(src, synthetic_driver_source()) is true
   - Expected: code equals `0`
   - Expected: stderr does not contain `driver registration did not increment static registry`
2. delete if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "/tmp/simple_driver_synthetic_registration_live.spl"
delete_if_exists(src)
expect(rt_file_write_text(src, synthetic_driver_source())).to_equal(true)

val (stdout, stderr, code) = rt_process_run(simple_cmd(), [src])
expect(code).to_equal(0)
expect(stderr.contains("driver registration did not increment static registry")).to_equal(false)

delete_if_exists(src)
```

</details>

#### executes register_static_driver for a stub-only @native_lib ops function

1. delete if exists
   - Expected: rt_file_write_text(src, synthetic_native_lib_source()) is true
   - Expected: code equals `0`
   - Expected: stderr does not contain `native-lib registration did not increment static registry`
2. delete if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "/tmp/simple_native_lib_synthetic_registration_live.spl"
delete_if_exists(src)
expect(rt_file_write_text(src, synthetic_native_lib_source())).to_equal(true)

val (stdout, stderr, code) = rt_process_run(simple_cmd(), [src])
expect(code).to_equal(0)
expect(stderr.contains("native-lib registration did not increment static registry")).to_equal(false)

delete_if_exists(src)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compiler/feature/driver_synthetic_registration_live_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FR-DRIVER-0001 live synthetic registration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
