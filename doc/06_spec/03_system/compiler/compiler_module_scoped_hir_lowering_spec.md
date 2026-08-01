# Compiler Module-Scoped HIR Lowering

> System-level regression check for FR-COMPILER-004. Each module must receive a

<!-- sdn-diagram:id=compiler_module_scoped_hir_lowering_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiler_module_scoped_hir_lowering_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiler_module_scoped_hir_lowering_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiler_module_scoped_hir_lowering_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Module-Scoped HIR Lowering

System-level regression check for FR-COMPILER-004. Each module must receive a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/compiler_module_scoped_hir_lowering_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

System-level regression check for FR-COMPILER-004. Each module must receive a
fresh HIR lowerer with an isolated symbol table and shared import context.

## Scenarios

### compiler module-scoped HIR lowering
_Module-local lowerers should share import context without sharing symbol tables._

#### creates a fresh symbol table for each module

1. var first = hirlowering for module
   - Expected: second.module_filename equals `b.spl`
   - Expected: second.symbols.next_symbol_id equals `0`
   - Expected: second.modules_by_name.keys().len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var modules: Dict<text, any> = {}
modules["a"] = "module-a"
modules["b"] = "module-b"

var first = hirlowering_for_module("a.spl", modules)
first.symbols.next_symbol_id = 42

val second = hirlowering_for_module("b.spl", modules)
expect(second.module_filename).to_equal("b.spl")
expect(second.symbols.next_symbol_id).to_equal(0)
expect(second.modules_by_name.keys().len()).to_equal(2)
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
