# Aop Weaving Config Specification

> <details>

<!-- sdn-diagram:id=aop_weaving_config_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aop_weaving_config_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aop_weaving_config_spec -> std
aop_weaving_config_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aop_weaving_config_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aop Weaving Config Specification

## Scenarios

### AOP Weaving Config

### WeavingConfig.disabled

#### creates disabled config with no rules

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = WeavingConfig.disabled()
expect(config.enabled).to_equal(false)
expect(weavingconfig_all_rules(config).len()).to_equal(0)
```

</details>

### WeavingConfig.from_rules

#### creates enabled config when rules present

1. WeavingRule
   - Expected: config.enabled is true
   - Expected: config.before_advices.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rules = [
    WeavingRule(predicate_text: "*", advice_function: "log_fn", form: AdviceForm.Before, priority: 10)
]
val config = WeavingConfig.from_rules(rules)
expect(config.enabled).to_equal(true)
expect(config.before_advices.len()).to_equal(1)
```

</details>

#### creates disabled config with empty rules

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = WeavingConfig.from_rules([])
expect(config.enabled).to_equal(false)
```

</details>

#### categorizes rules by advice form

1. WeavingRule
2. WeavingRule
3. WeavingRule
4. WeavingRule
   - Expected: config.before_advices.len() equals `1`
   - Expected: config.after_success_advices.len() equals `1`
   - Expected: config.after_error_advices.len() equals `1`
   - Expected: config.around_advices.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rules = [
    WeavingRule(predicate_text: "*", advice_function: "before_fn", form: AdviceForm.Before, priority: 10),
    WeavingRule(predicate_text: "*", advice_function: "after_fn", form: AdviceForm.AfterSuccess, priority: 10),
    WeavingRule(predicate_text: "*", advice_function: "error_fn", form: AdviceForm.AfterError, priority: 10),
    WeavingRule(predicate_text: "*", advice_function: "around_fn", form: AdviceForm.Around, priority: 10)
]
val config = WeavingConfig.from_rules(rules)
expect(config.before_advices.len()).to_equal(1)
expect(config.after_success_advices.len()).to_equal(1)
expect(config.after_error_advices.len()).to_equal(1)
expect(config.around_advices.len()).to_equal(1)
```

</details>

### matches_predicate

#### matches wildcard predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = JoinPointContext(function_name: "foo", module_path: "mod", signature: "", attributes: [], effects: [])
expect(matches_predicate("*", ctx)).to_equal(true)
```

</details>

#### matches exact function name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = JoinPointContext(function_name: "my_func", module_path: "mod", signature: "", attributes: [], effects: [])
expect(matches_predicate("my_func", ctx)).to_equal(true)
```

</details>

#### rejects non-matching function name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = JoinPointContext(function_name: "other", module_path: "mod", signature: "", attributes: [], effects: [])
expect(matches_predicate("my_func", ctx)).to_equal(false)
```

</details>

#### matches attribute predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = JoinPointContext(function_name: "foo", module_path: "mod", signature: "", attributes: ["logged"], effects: [])
expect(matches_predicate("@logged", ctx)).to_equal(true)
```

</details>

#### matches module predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = JoinPointContext(function_name: "foo", module_path: "services.auth", signature: "", attributes: [], effects: [])
expect(matches_predicate("module:services.*", ctx)).to_equal(true)
```

</details>

### predicate_specificity

#### assigns wildcard lowest specificity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(predicate_specificity("*")).to_equal(0)
```

</details>

#### assigns glob pattern specificity 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(predicate_specificity("foo*")).to_equal(1)
```

</details>

#### assigns attribute specificity 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(predicate_specificity("@logged")).to_equal(2)
```

</details>

#### assigns module specificity 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(predicate_specificity("module:services")).to_equal(3)
```

</details>

#### assigns exact name highest specificity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(predicate_specificity("my_exact_func")).to_equal(4)
```

</details>

### weave_function

#### returns empty result for disabled config

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = WeavingConfig.disabled()
val blocks: [MirBlockInfo] = []
val result = weave_function(config, "test_fn", "mod", [], [], blocks)
expect(result.advices_inserted).to_equal(0)
expect(result.join_points_woven).to_equal(0)
```

</details>

#### returns empty result for function with no matching advice

1. WeavingRule
   - Expected: result.advices_inserted equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rules = [
    WeavingRule(predicate_text: "specific_fn", advice_function: "log_fn", form: AdviceForm.Before, priority: 10)
]
val config = WeavingConfig.from_rules(rules)
val blocks = [MirBlockInfo(id: 0, instruction_kinds: [InstructionInfo(index: 0, kind_tag: "call")])]
val result = weave_function(config, "other_fn", "mod", [], [], blocks)
expect(result.advices_inserted).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/aop_weaving_config_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AOP Weaving Config
- WeavingConfig.disabled
- WeavingConfig.from_rules
- matches_predicate
- predicate_specificity
- weave_function

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
