# Simpleos Tools Toolchain Paths Specification

> <details>

<!-- sdn-diagram:id=simpleos_tools_toolchain_paths_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_tools_toolchain_paths_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_tools_toolchain_paths_spec -> std
simpleos_tools_toolchain_paths_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_tools_toolchain_paths_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Tools Toolchain Paths Specification

## Scenarios

### simpleos-tools toolchain paths

#### ships stable native command paths and manifests for the guest toolchain surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = _find_tools_files()
expect(files).to_contain("/usr/bin/cmake")
expect(files).to_contain("/usr/bin/ninja")
expect(files).to_contain("/SYS/CMAKEVER.TXT")
expect(files).to_contain("/SYS/CMAKEMAN.TXT")
expect(files).to_contain("/SYS/NINJAVER.TXT")
expect(files).to_contain("/SYS/NINJAMAN.TXT")
expect(files).to_contain("/SYS/LLVMMAN.TXT")
expect(files).to_contain("/SYS/CLANGMAN.TXT")
expect(files).to_contain("/SYS/RUSTMAN.TXT")
expect(files).to_contain("/usr/share/simpleos/toolchain/llvm/hello.ll")
expect(files).to_contain("/usr/share/simpleos/toolchain/llvm/pipeline.step")
expect(files).to_contain("/usr/share/simpleos/toolchain/clang/hello.c")
expect(files).to_contain("/usr/share/simpleos/toolchain/clang/pipeline.step")
expect(files).to_contain("/usr/share/simpleos/toolchain/rust/hello.rs")
expect(files).to_contain("/usr/share/simpleos/toolchain/rust/pipeline.step")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/packages/simpleos_tools_toolchain_paths_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- simpleos-tools toolchain paths

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
