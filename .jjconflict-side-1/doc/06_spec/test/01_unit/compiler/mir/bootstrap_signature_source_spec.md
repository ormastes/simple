# Bootstrap Signature Source Specification

> <details>

<!-- sdn-diagram:id=bootstrap_signature_source_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bootstrap_signature_source_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bootstrap_signature_source_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bootstrap_signature_source_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Signature Source Specification

## Scenarios

### bootstrap MIR signature source shape

#### does not hardcode generic bootstrap stubs to i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = module_lowering_source()
expect(source.contains("me bootstrap_function_signature(name: text) -> MirSignature:")).to_equal(true)
expect(source.contains("val signature = self.bootstrap_function_signature(name)")).to_equal(true)
expect(source.contains("val signature = MirSignature(params: [], return_type: MirType.i64(), is_variadic: false)\n        var bldr = self.builder\n        bldr.begin_function(symbol, name, signature")).to_equal(false)
```

</details>

#### returns typed zero for non-unit bootstrap fallback results

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = module_lowering_source()
expect(source.contains("fn bootstrap_default_return_operand(return_type: MirType) -> MirOperand?:")).to_equal(true)
expect(source.contains("MirConstValue.Zero, return_type")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `/home/ormastes/dev/pub/simple-worktrees/phase3-bootstrap/test/01_unit/compiler/mir/bootstrap_signature_source_spec.spl` |
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- bootstrap MIR signature source shape

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
