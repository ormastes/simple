# Domain Block HIR Lowering Unit Spec

> Verifies that top-level domain blocks survive the pure Simple frontend and

<!-- sdn-diagram:id=domain_block_hir_lowering_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=domain_block_hir_lowering_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

domain_block_hir_lowering_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=domain_block_hir_lowering_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Domain Block HIR Lowering Unit Spec

Verifies that top-level domain blocks survive the pure Simple frontend and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/domain_block_hir_lowering_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies that top-level domain blocks survive the pure Simple frontend and
arrive in HIR metadata without stealing ordinary identifier usage.

## Scenarios

### domain block HIR lowering

#### captures schema and style blocks at module scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = make_logger()
val source = "schema{Building: id Uuid}\nstyle{Button.primary: padding 8px}"
val module = parse_full_frontend(source, "domain_blocks", "domain_blocks", log)

expect(module.domain_blocks.len()).to_equal(2)
expect(module.domain_blocks[0].kind).to_equal("schema")
expect(module.domain_blocks[0].payload).to_equal("Building: id Uuid")
expect(module.domain_blocks[0].context).to_equal("module")
expect(module.domain_blocks[1].kind).to_equal("style")
expect(module.domain_blocks[1].payload).to_equal("Button.primary: padding 8px")

val hir = HirLowering.with_filename("domain_blocks").lower_module(module)
expect(hir.domain_blocks.len()).to_equal(2)
expect(hir.domain_blocks[0].kind).to_equal("schema")
expect(hir.domain_blocks[0].payload).to_equal("Building: id Uuid")
expect(hir.domain_blocks[1].kind).to_equal("style")
expect(hir.domain_blocks[1].payload).to_equal("Button.primary: padding 8px")
```

</details>

#### does not treat ordinary schema identifiers as domain blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = make_logger()
val source = "val schema = 1"
val module = parse_full_frontend(source, "schema_ident", "schema_ident", log)

expect(module.domain_blocks.len()).to_equal(0)
expect(module.constants.has("schema")).to_equal(true)
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
