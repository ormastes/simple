# Dynamic Driver Lsm Packaging Specification

> 1. delete if exists

<!-- sdn-diagram:id=dynamic_driver_lsm_packaging_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dynamic_driver_lsm_packaging_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dynamic_driver_lsm_packaging_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dynamic_driver_lsm_packaging_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dynamic Driver Lsm Packaging Specification

## Scenarios

### dynamic driver LSM packaging

#### bin/simple compile --driver-mode=dynamic writes LSMF with SMF and DRVS bytes

1. delete if exists
   - Expected: rt_file_write_text(src, "@driver(class = 2, vendor = 0x1B36, device = [0x000E], version = \"1.0\")\nfn driver_init():\n    return 0\n") is true
   - Expected: code equals `0`
   - Expected: rt_file_exists(out) is true
   - Expected: archive[0] equals `76`
   - Expected: archive[1] equals `83`
   - Expected: archive[2] equals `77`
   - Expected: archive[3] equals `70`
   - Expected: archive[smf_offset] equals `83`
   - Expected: archive[smf_offset + 1] equals `77`
   - Expected: archive[smf_offset + 2] equals `70`
   - Expected: archive[smf_offset + 3] equals `0`
   - Expected: contains_ascii(archive, [46, 100, 114, 118, 95, 109, 97, 110, 105, 102, 101, 115, 116]) is true
   - Expected: contains_ascii(archive, [83, 86, 82, 68]) is true
2. delete if exists
3. delete if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "/tmp/simple_dynamic_driver_lsm_packaging.spl"
val out = "/tmp/simple_dynamic_driver_lsm_packaging.lsm"
delete_if_exists(out)
expect(rt_file_write_text(src, "@driver(class = 2, vendor = 0x1B36, device = [0x000E], version = \"1.0\")\nfn driver_init():\n    return 0\n")).to_equal(true)

val (stdout, stderr, code) = rt_process_run("bin/simple", ["compile", "--driver-mode=dynamic", src, "-o", out])
expect(code).to_equal(0)
expect(rt_file_exists(out)).to_equal(true)

val archive = rt_file_read_bytes(out) ?? []
expect(archive[0]).to_equal(76)
expect(archive[1]).to_equal(83)
expect(archive[2]).to_equal(77)
expect(archive[3]).to_equal(70)

val smf_offset = le_u64(archive, 128 + 64)
expect(archive[smf_offset]).to_equal(83)
expect(archive[smf_offset + 1]).to_equal(77)
expect(archive[smf_offset + 2]).to_equal(70)
expect(archive[smf_offset + 3]).to_equal(0)
expect(contains_ascii(archive, [46, 100, 114, 118, 95, 109, 97, 110, 105, 102, 101, 115, 116])).to_equal(true)
expect(contains_ascii(archive, [83, 86, 82, 68])).to_equal(true)

delete_if_exists(src)
delete_if_exists(out)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/dynamic_driver_lsm_packaging_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- dynamic driver LSM packaging

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
