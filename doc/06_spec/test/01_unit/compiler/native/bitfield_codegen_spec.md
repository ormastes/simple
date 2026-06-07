# Bitfield Codegen Specification

> <details>

<!-- sdn-diagram:id=bitfield_codegen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bitfield_codegen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bitfield_codegen_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bitfield_codegen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bitfield Codegen Specification

## Scenarios

### Bitfield Codegen

#### registers bitfield declarations during Rust seed HIR lowering

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_pass = rt_file_read_text("src/compiler_rust/compiler/src/hir/lower/module_lowering/module_pass.rs") ?? ""
expect(module_pass.contains("Node::Bitfield(bf) =>")).to_equal(true)
expect(module_pass.contains("self.register_bitfield(bf)?")).to_equal(true)
expect(module_pass.contains("Node::Bitfield(_)")).to_equal(false)
```

</details>

#### registers bitfield declarations in statement and interpreter paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stmt_lowering = rt_file_read_text("src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs") ?? ""
val interpreter_eval = rt_file_read_text("src/compiler_rust/compiler/src/interpreter_eval.rs") ?? ""
expect(stmt_lowering.contains("Node::Bitfield(bf) =>")).to_equal(true)
expect(stmt_lowering.contains("self.register_bitfield(bf)?")).to_equal(true)
expect(interpreter_eval.contains("Node::Bitfield(bitfield) =>")).to_equal(true)
expect(interpreter_eval.contains("super::register_bitfield(bitfield)")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/native/bitfield_codegen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Bitfield Codegen

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
