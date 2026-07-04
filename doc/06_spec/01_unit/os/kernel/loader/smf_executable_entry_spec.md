# Smf Executable Entry Specification

> <details>

<!-- sdn-diagram:id=smf_executable_entry_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_executable_entry_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_executable_entry_spec -> std
smf_executable_entry_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smf_executable_entry_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smf Executable Entry Specification

## Scenarios

### SMF executable entry helper

#### returns the typed entry point for an x86_64 executable envelope

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = _smf_exec_fixture(1)
val entry = smf_executable_entry_point_for_arch(bytes, Architecture.X86_64)
expect(entry.is_ok()).to_equal(true)
expect(entry.unwrap()).to_equal(0x1234)
```

</details>

#### rejects an executable envelope for the wrong architecture

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = _smf_exec_fixture(3)
val entry = smf_executable_entry_point_for_arch(bytes, Architecture.X86_64)
expect(entry.is_err()).to_equal(true)
expect(entry.unwrap_err()).to_equal(SMF_ERR_WRONG_ARCH)
```

</details>

#### extracts the same embedded ELF stub used by filesystem spawn

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = _smf_exec_fixture(1)
val stub = smf_extract_executable_stub_for_arch(bytes, Architecture.X86_64)
expect(stub.is_ok()).to_equal(true)
expect(stub.unwrap().len()).to_equal(8)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/smf_executable_entry_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SMF executable entry helper

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
