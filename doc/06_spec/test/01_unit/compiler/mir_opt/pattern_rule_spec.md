# PatternRulePass Specification

> Validates the data-driven PatternRule schema model which loads `.opt.json` rule files and retains named pattern/rewrite metadata. Production MIR execution remains quarantined until legality proofs exist.

<!-- sdn-diagram:id=pattern_rule_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pattern_rule_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pattern_rule_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pattern_rule_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# PatternRulePass Specification

Validates the data-driven PatternRule schema model which loads `.opt.json` rule files and retains named pattern/rewrite metadata. Production MIR execution remains quarantined until legality proofs exist.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #web-server-optimizer-complete |
| Category | Compiler / MIR Optimization — Rule Engine |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/compiler/mir_opt/pattern_rule_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the data-driven PatternRule schema model which loads `.opt.json`
rule files and retains named pattern/rewrite metadata. Production MIR
execution remains quarantined until legality proofs exist. The AC-7 schema extends `simple.opt.mir.v1` with an
optional `rules: [PatternRule]` array.

## Behavior

- Rule file with valid schema is loaded without error
- Pattern matching finds the expected instruction sequence
- Rewrite metadata is retained; the production pass returns MIR unchanged
- Opaque rewrite metadata remains loadable for v1 compatibility
- Cost metadata is retained but does not authorize application

## Scenarios

### PatternRulePass

### rule file loading

#### loads .opt.json rule file and validates schema

- pattern: "BinOp:Add
- rewrite: "Copy
   - Expected: result.ok is true
   - Expected: result.rules.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rules = [
    PatternRule(
        name: "add_zero_elim",
        pattern: "BinOp:Add(%x, 0)",
        rewrite: "Copy(%x)",
        cost_delta: -1
    )
]
val result = load_opt_json("simple.opt.mir.v1", rules)
expect(result.ok).to_equal(true)
expect(result.rules.len()).to_equal(1)
```

</details>

#### retains opaque rule metadata for v1 compatibility

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_rules = [
    PatternRule(
        name: "bad_rule",
        pattern: "",
        rewrite: "Nop",
        cost_delta: 0
    )
]
val result = load_opt_json("simple.opt.mir.v1", bad_rules)
expect(result.ok).to_equal(true)
expect(result.rules.len()).to_equal(1)
```

</details>

#### rejects file with unknown schema version

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rules: List<PatternRule> = []
val result = load_opt_json("simple.opt.mir.v99", rules)
expect(result.ok).to_equal(false)
expect(result.error_msg).to_contain("unknown schema")
```

</details>

### pattern matching

#### matches MIR pattern against instruction sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instructions = [
    "Load %ptr",
    "BinOp:Add %a 0",
    "Store %dst"
]
val match_idx = find_pattern(instructions, "BinOp:Add")
expect(match_idx).to_equal(1)
```

</details>

#### returns -1 when pattern is not present in sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instructions = ["Load %ptr", "Store %dst"]
val match_idx = find_pattern(instructions, "BinOp:Mul")
expect(match_idx).to_equal(-1)
```

</details>

### rewrite application

#### quarantines rewrite metadata and preserves instructions

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instructions = ["Load %ptr", "BinOp:Add %a 0", "Store %dst"]
val match_idx = 1
val rewritten = apply_rewrite(instructions, match_idx, "Copy %a")
expect(rewritten.len()).to_equal(3)
expect(rewritten[1]).to_equal("BinOp:Add %a 0")
expect(rewritten[0]).to_equal("Load %ptr")
expect(rewritten[2]).to_equal("Store %dst")
```

</details>

### cost reporting

#### retains cost delta without authorizing a rewrite

- pattern: "BinOp:Mul
- rewrite: "BinOp:Shl
   - Expected: rule.cost_delta equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = PatternRule(
    name: "strength_reduce_mul2",
    pattern: "BinOp:Mul(%x, 2)",
    rewrite: "BinOp:Shl(%x, 1)",
    cost_delta: -2
)
expect(rule.cost_delta).to_equal(-2)
expect(rule.cost_delta).to_be_less_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
