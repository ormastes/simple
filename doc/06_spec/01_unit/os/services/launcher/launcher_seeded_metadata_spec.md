# Launcher Seeded Metadata Specification

> <details>

<!-- sdn-diagram:id=launcher_seeded_metadata_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=launcher_seeded_metadata_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

launcher_seeded_metadata_spec -> std
launcher_seeded_metadata_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=launcher_seeded_metadata_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Launcher Seeded Metadata Specification

## Scenarios

### Launcher seeded app metadata

#### resolves Simple tool aliases through one seeded metadata table

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_seeded_app_name_for_path("/sys/apps/simple_browser")).to_equal("Simple Browser")
expect(_seeded_app_name_for_path("/sys/apps/sbrowser.smf")).to_equal("Simple Browser")
expect(_seeded_app_icon_for_path("/SYS/APPS/SBROWSMF.SMF")).to_equal("W")
expect(_seeded_app_key_for_path("/SYS/APPS/SBROWSMF.SMF")).to_equal(0x57)

expect(_seeded_app_name_for_path("/sys/apps/simple_compiler.smf")).to_equal("Simple Compiler")
expect(_seeded_app_icon_for_path("/SYS/APPS/SCOMPSMF.SMF")).to_equal("C")
expect(_seeded_app_key_for_path("/SYS/APPS/SCOMPSMF.SMF")).to_equal(0x43)

expect(_seeded_app_name_for_path("/sys/apps/simple_loader.smf")).to_equal("Simple Loader")
expect(_seeded_app_icon_for_path("/SYS/APPS/SLOADSMF.SMF")).to_equal("O")
expect(_seeded_app_key_for_path("/SYS/APPS/SLOADSMF.SMF")).to_equal(0x4F)

expect(_seeded_app_name_for_path("/sys/apps/simple.smf")).to_equal("Simple")
expect(_seeded_app_name_for_path("/usr/bin/simple")).to_equal("Simple")
expect(_seeded_app_icon_for_path("/SYS/APPS/SIMPLSTC.SMF")).to_equal("S")
expect(_seeded_app_key_for_path("/SYS/APPS/SIMPLSTC.SMF")).to_equal(0x53)
```

</details>

#### resolves toolchain app aliases through one seeded metadata table

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_seeded_app_name_for_path("/sys/apps/llvm.smf")).to_equal("LLVM")
expect(_seeded_app_icon_for_path("/SYS/APPS/LLVMSMF.SMF")).to_equal("L")
expect(_seeded_app_key_for_path("/SYS/APPS/LLVMSMF.SMF")).to_equal(0x4C)

expect(_seeded_app_name_for_path("/sys/apps/clang.smf")).to_equal("Clang")
expect(_seeded_app_icon_for_path("/SYS/APPS/CLANGSMF.SMF")).to_equal("K")
expect(_seeded_app_key_for_path("/SYS/APPS/CLANGSMF.SMF")).to_equal(0x47)

expect(_seeded_app_name_for_path("/sys/apps/rust.smf")).to_equal("Rust")
expect(_seeded_app_icon_for_path("/SYS/APPS/RUSTSMF.SMF")).to_equal("R")
expect(_seeded_app_key_for_path("/SYS/APPS/RUSTSMF.SMF")).to_equal(0x52)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/launcher/launcher_seeded_metadata_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Launcher seeded app metadata

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
