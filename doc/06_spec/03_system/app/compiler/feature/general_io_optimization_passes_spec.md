# General Io Optimization Passes Specification

> <details>

<!-- sdn-diagram:id=general_io_optimization_passes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=general_io_optimization_passes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

general_io_optimization_passes_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=general_io_optimization_passes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# General Io Optimization Passes Specification

## Scenarios

### CLibParityHotspot Provider Registration

### bulk_copy provider

#### has CLibParityHotspot kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = optimization_rule_provider_bulk_copy("simple.opt.mir.bulk_copy")
expect(p.kind).to_equal(OptimizerProviderKind.CLibParityHotspot)
```

</details>

#### is hot_path and enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = optimization_rule_provider_bulk_copy("simple.opt.mir.bulk_copy")
expect(p.hot_path).to_equal(true)
expect(p.enabled).to_equal(true)
```

</details>

#### uses PipelinePass lookup

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = optimization_rule_provider_bulk_copy("simple.opt.mir.bulk_copy")
expect(p.lookup_kind).to_equal(OptimizerRuleLookupKind.PipelinePass)
```

</details>

#### produces bulk_copy_rewrite fact

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = optimization_rule_provider_bulk_copy("simple.opt.mir.bulk_copy")
expect(p.produced_facts.len()).to_be_greater_than(0)
```

</details>

### bulk_fill provider

#### has CLibParityHotspot kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = optimization_rule_provider_bulk_fill("simple.opt.mir.bulk_fill")
expect(p.kind).to_equal(OptimizerProviderKind.CLibParityHotspot)
```

</details>

#### is hot_path and enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = optimization_rule_provider_bulk_fill("simple.opt.mir.bulk_fill")
expect(p.hot_path).to_equal(true)
expect(p.enabled).to_equal(true)
```

</details>

### bulk_cmp provider

#### has CLibParityHotspot kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = optimization_rule_provider_bulk_cmp("simple.opt.mir.bulk_cmp")
expect(p.kind).to_equal(OptimizerProviderKind.CLibParityHotspot)
```

</details>

#### is hot_path and enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = optimization_rule_provider_bulk_cmp("simple.opt.mir.bulk_cmp")
expect(p.hot_path).to_equal(true)
expect(p.enabled).to_equal(true)
```

</details>

### endian_load provider

#### has CLibParityHotspot kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = optimization_rule_provider_endian_load("simple.opt.mir.endian_load")
expect(p.kind).to_equal(OptimizerProviderKind.CLibParityHotspot)
```

</details>

#### is hot_path and enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = optimization_rule_provider_endian_load("simple.opt.mir.endian_load")
expect(p.hot_path).to_equal(true)
expect(p.enabled).to_equal(true)
```

</details>

### endian_store provider

#### has CLibParityHotspot kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = optimization_rule_provider_endian_store("simple.opt.mir.endian_store")
expect(p.kind).to_equal(OptimizerProviderKind.CLibParityHotspot)
```

</details>

#### is hot_path and enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = optimization_rule_provider_endian_store("simple.opt.mir.endian_store")
expect(p.hot_path).to_equal(true)
expect(p.enabled).to_equal(true)
```

</details>

### Provider Generality

#### bulk_copy requires typed_mir not fs-specific facts

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = optimization_rule_provider_bulk_copy("simple.opt.mir.bulk_copy")
expect(p.safety_class).to_equal("pure")
expect(p.required_facts.len()).to_be_greater_than(0)
```

</details>

#### endian_load requires shift_or_chain not fs-specific facts

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = optimization_rule_provider_endian_load("simple.opt.mir.endian_load")
expect(p.safety_class).to_equal("pure")
```

</details>

#### endian_store requires shift_and_store_chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = optimization_rule_provider_endian_store("simple.opt.mir.endian_store")
expect(p.safety_class).to_equal("pure")
```

</details>

#### existing clib_parity provider still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = optimization_rule_provider_clib_parity("simple.opt.mir.clib_parity", true)
expect(p.kind).to_equal(OptimizerProviderKind.CLibParityHotspot)
expect(p.hot_path).to_equal(true)
```

</details>

### Provider Fact Gating

#### bulk_copy can run when required facts are present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = optimization_rule_provider_bulk_copy("simple.opt.mir.bulk_copy")
val facts = ["typed_mir", "gep_contiguous"]
expect(optimization_rule_provider_can_run(p, facts)).to_equal(true)
```

</details>

#### bulk_copy cannot run when facts are missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = optimization_rule_provider_bulk_copy("simple.opt.mir.bulk_copy")
val empty_facts: [text] = []
expect(optimization_rule_provider_can_run(p, empty_facts)).to_equal(false)
```

</details>

#### endian_load can run when shift_or_chain fact is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = optimization_rule_provider_endian_load("simple.opt.mir.endian_load")
val facts = ["typed_mir", "shift_or_chain"]
expect(optimization_rule_provider_can_run(p, facts)).to_equal(true)
```

</details>

#### endian_store cannot run without shift_and_store_chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = optimization_rule_provider_endian_store("simple.opt.mir.endian_store")
val facts = ["typed_mir"]
expect(optimization_rule_provider_can_run(p, facts)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compiler/feature/general_io_optimization_passes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CLibParityHotspot Provider Registration
- bulk_copy provider
- bulk_fill provider
- bulk_cmp provider
- endian_load provider
- endian_store provider
- Provider Generality
- Provider Fact Gating

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
