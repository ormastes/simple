# Native Backend Specification

> <details>

<!-- sdn-diagram:id=native_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_backend_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Backend Specification

## Scenarios

### Native Backend

#### keeps ELF byte-buffer primitives available

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_native_source("src/compiler/70.backend/backend/native/elf_writer.spl")

expect(source).to_contain("struct ByteBuffer")
expect(source).to_contain("fn new_byte_buffer() -> ByteBuffer")
```

</details>

#### keeps machine instruction register constructors available

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_native_source("src/compiler/70.backend/backend/native/mach_inst.spl")

expect(source).to_contain("struct MachReg")
expect(source).to_contain("fn virtual_reg(id: i64) -> MachReg")
```

</details>

#### keeps register allocation and x86 encoding entrypoints available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val regalloc_source = read_native_source("src/compiler/70.backend/backend/native/regalloc.spl")
val encode_source = read_native_source("src/compiler/70.backend/backend/native/encode_x86_64.spl")

expect(regalloc_source).to_contain("fn linear_scan_x86_64")
expect(encode_source).to_contain("fn encode_function(func: MachFunction)")
```

</details>

#### keeps native module target entrypoints available

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_native_source("src/compiler/70.backend/backend/native/mod.spl")

expect(source).to_contain("fn compile_native_x86_64(module: MirModule)")
expect(source).to_contain("fn target_to_arch_byte(target: CodegenTarget)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Native Backend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
