# Pipeline Native

> Tests the native compilation pipeline stages from parsing through MIR lowering to native code emission. Verifies that each pipeline stage correctly transforms its input and that the full pipeline produces working native executables.

<!-- sdn-diagram:id=pipeline_native_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pipeline_native_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pipeline_native_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pipeline_native_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pipeline Native

Tests the native compilation pipeline stages from parsing through MIR lowering to native code emission. Verifies that each pipeline stage correctly transforms its input and that the full pipeline produces working native executables.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/pipeline_native_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the native compilation pipeline stages from parsing through MIR lowering
to native code emission. Verifies that each pipeline stage correctly transforms
its input and that the full pipeline produces working native executables.

## Scenarios

### Pipeline Native

#### compiles fn main() -> exit 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_link("fn main():\n    0\n")
    expect(code).to_equal(0)
```

</details>

#### produces non-empty ELF bytes

1. var parser = Parser new
2. var hir lowering = HirLowering new
3. var mir lowering ctx = MirLowering new
   - Expected: elf_bytes.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val source = "fn main():\n    0\n"
    var parser = Parser.new(source)
    val ast_module = parser.parse()
    var hir_lowering = HirLowering.new()
    val hir_module = hir_lowering.lower_module(ast_module)
    var mir_lowering_ctx = MirLowering.new(hir_lowering.symbols)
    val mir_module = mir_lowering_ctx.lower_module(hir_module)
    val elf_bytes = compile_native(mir_module, CodegenTarget.X86_64)
    expect(elf_bytes.len() > 0).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
