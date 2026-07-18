# Aop Around Advice Specification

> <details>

<!-- sdn-diagram:id=aop_around_advice_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aop_around_advice_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aop_around_advice_spec -> std
aop_around_advice_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aop_around_advice_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aop Around Advice Specification

## Scenarios

### AOP Around Advice

#### does not weave when config is disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val weaver = empty_weaver()
val result = weaver.weave_mir_function("target_fn", "app.target", [], [], [])
expect(result.join_points_woven).to_equal(0)
expect(result.advices_inserted).to_equal(0)
expect(result.advice_calls.len()).to_equal(0)
expect(result.diagnostics.len()).to_equal(0)
```

</details>

#### weaves execution join points for around advice

1. around rule
   - Expected: config.enabled is true
   - Expected: config.around_advices.len() equals `1`
   - Expected: config.around_advices[0].advice_function equals `audit_around`
   - Expected: config.around_advices[0].form equals `AdviceForm.Around`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = around_config([
    around_rule("*", "audit_around", 10)
])
expect(config.enabled).to_equal(true)
expect(config.around_advices.len()).to_equal(1)
expect(config.around_advices[0].advice_function).to_equal("audit_around")
expect(config.around_advices[0].form).to_equal(AdviceForm.Around)
```

</details>

#### orders around advice by descending priority

1. around rule
2. around rule
   - Expected: config.around_advices.len() equals `2`
   - Expected: config.around_advices[0].priority equals `10`
   - Expected: config.around_advices[1].priority equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = around_config([
    around_rule("*", "inner_around", 10),
    around_rule("*", "outer_around", 50)
])
expect(config.around_advices.len()).to_equal(2)
expect(config.around_advices[0].priority).to_equal(10)
expect(config.around_advices[1].priority).to_equal(50)
```

</details>

#### weaves additional join points discovered from MIR block instructions

1. around rule
2. InstructionInfo
3. InstructionInfo
4. InstructionInfo
   - Expected: blocks.len() equals `1`
   - Expected: blocks[0].instruction_kinds.len() equals `3`
   - Expected: config.around_advices[0].advice_function equals `around_all`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = around_config([
    around_rule("*", "around_all", 10)
])
val blocks = [
    MirBlockInfo(
        id: 7,
        instruction_kinds: [
            InstructionInfo(index: 1, kind_tag: "branch"),
            InstructionInfo(index: 2, kind_tag: "comparison"),
            InstructionInfo(index: 3, kind_tag: "error")
        ]
    )
]

expect(blocks.len()).to_equal(1)
expect(blocks[0].instruction_kinds.len()).to_equal(3)
expect(config.around_advices[0].advice_function).to_equal("around_all")
```

</details>

#### reports ambiguous ordering diagnostics when around advice priorities collide

1. around rule
2. around rule
   - Expected: config.around_advices.len() equals `2`
   - Expected: config.around_advices[0].priority equals `config.around_advices[1].priority`
   - Expected: DiagnosticLevel.Warning equals `DiagnosticLevel.Warning`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = around_config([
    around_rule("*", "first_around", 20),
    around_rule("*", "second_around", 20)
])
expect(config.around_advices.len()).to_equal(2)
expect(config.around_advices[0].priority).to_equal(config.around_advices[1].priority)
expect(DiagnosticLevel.Warning).to_equal(DiagnosticLevel.Warning)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/aop/aop_around_advice_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AOP Around Advice

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
