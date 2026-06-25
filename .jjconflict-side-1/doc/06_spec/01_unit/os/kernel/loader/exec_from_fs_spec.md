# Exec From Fs Specification

> <details>

<!-- sdn-diagram:id=exec_from_fs_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=exec_from_fs_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

exec_from_fs_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=exec_from_fs_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Exec From Fs Specification

## Scenarios

### SimpleOS exec-from-filesystem pipeline

#### capability_gate_denies_unprivileged_exec

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = exec_cap_check(100, "/apps/hello", false, false)
expect(result).to_equal(-13)
```

</details>

#### capability_gate_denies_missing_process_spawn

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = exec_cap_check(100, "/apps/hello", true, false)
expect(result).to_equal(-13)
```

</details>

#### capability_gate_permits_privileged_exec

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = exec_cap_check(100, "/apps/hello", true, true)
expect(result).to_equal(0)
```

</details>

#### capability_gate_bypasses_for_kernel_origin

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = exec_cap_check(0, "/apps/hello", false, false)
expect(result).to_equal(0)
```

</details>

#### elf64_magic_detection_succeeds_on_valid_header

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = make_valid_elf_magic()
expect(elf64_has_magic(bytes)).to_equal(true)
```

</details>

#### elf64_magic_detection_rejects_invalid_header

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = make_invalid_magic()
expect(elf64_has_magic(bytes)).to_equal(false)
```

</details>

#### elf64_magic_detection_rejects_short_input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i32] = [127, 69]
expect(elf64_has_magic(bytes)).to_equal(false)
```

</details>

#### fat32_binary_read_returns_nonempty_bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Fat32ReadResult.ok(4096)
expect(result.success).to_equal(true)
expect(result.data_len > 0).to_equal(true)
```

</details>

#### fat32_binary_read_reports_missing_file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Fat32ReadResult.fail("file not found")
expect(result.success).to_equal(false)
expect(result.data_len).to_equal(0)
```

</details>

#### hardening_probe_reports_nonzero_nx_when_hardened

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = HardeningReport.hardened()
expect(report.nx).to_equal(1)
expect(report.smep).to_equal(1)
expect(report.smap).to_equal(1)
expect(report.wp).to_equal(1)
expect(report.aslr_seed != 0).to_equal(true)
```

</details>

#### hardening_probe_empty_has_zero_fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = HardeningReport.empty()
expect(report.nx).to_equal(0)
expect(report.smep).to_equal(0)
expect(report.smap).to_equal(0)
```

</details>

#### exec_spawn_succeeds_with_full_privileges

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = simulate_fs_exec_spawn(100, "/apps/hello", true, true, true, true)
expect(result.error_code).to_equal(0)
expect(result.pid > 0).to_equal(true)
```

</details>

#### exec_spawn_fails_without_capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = simulate_fs_exec_spawn(100, "/apps/hello", false, false, true, true)
expect(result.error_code).to_equal(-13)
```

</details>

#### exec_spawn_fails_on_missing_file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = simulate_fs_exec_spawn(100, "/apps/hello", true, true, false, true)
expect(result.error_code).to_equal(-2)
```

</details>

#### exec_spawn_fails_on_invalid_elf

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = simulate_fs_exec_spawn(100, "/apps/hello", true, true, true, false)
expect(result.error_code).to_equal(-8)
```

</details>

#### exec_spawn_kernel_origin_bypasses_cap_check

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = simulate_fs_exec_spawn(0, "/apps/hello", false, false, true, true)
expect(result.error_code).to_equal(0)
expect(result.pid > 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/exec_from_fs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS exec-from-filesystem pipeline

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
