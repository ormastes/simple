# Direct ELF Writing - Basic Configuration

> Tests the basic configuration of the direct ELF writer including header generation, section layout, and symbol table construction. Verifies that minimal ELF binaries are correctly structured and loadable by the operating system.

<!-- sdn-diagram:id=direct_elf_basic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=direct_elf_basic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

direct_elf_basic_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=direct_elf_basic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Direct ELF Writing - Basic Configuration

Tests the basic configuration of the direct ELF writer including header generation, section layout, and symbol table construction. Verifies that minimal ELF binaries are correctly structured and loadable by the operating system.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/linker/direct_elf_basic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the basic configuration of the direct ELF writer including header generation,
section layout, and symbol table construction. Verifies that minimal ELF binaries
are correctly structured and loadable by the operating system.

## Scenarios

### Direct ELF Writing - Basic

#### check default setting

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = should_use_direct_elf_writing()
expect(result).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
