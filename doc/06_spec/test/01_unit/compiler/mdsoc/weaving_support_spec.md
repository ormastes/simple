# Weaving Support Specification

> <details>

<!-- sdn-diagram:id=weaving_support_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=weaving_support_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

weaving_support_spec -> compiler
weaving_support_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=weaving_support_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Weaving Support Specification

## Scenarios

### MDSOC weaving support types

#### constructs matched advice and weaving rules

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matched = MatchedAdvice(
    advice_function: "security.auth_before",
    form: AdviceForm.Before,
    priority: 10,
    specificity: 2
)
val rule = WeavingRule(
    predicate_text: "@authenticated",
    advice_function: matched.advice_function,
    form: matched.form,
    priority: matched.priority
)
expect(rule.predicate_text).to_equal("@authenticated")
expect(rule.advice_function).to_equal("security.auth_before")
expect(rule.priority).to_equal(10)
```

</details>

#### creates an empty weaving result

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = weavingresult_new()
expect(result.join_points_woven).to_equal(0)
expect(result.advices_inserted).to_equal(0)
expect(result.advice_calls.len()).to_equal(0)
expect(result.diagnostics.len()).to_equal(0)
```

</details>

### deny advice

#### returns maintenance denial for annotated join points

1. signature: "fn
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = JoinPointContext(
    function_name: "handle_request",
    module_path: "std.http.admin",
    signature: "fn()",
    attributes: ["peer=198.51.100.42", "deny_all"],
    effects: []
)
val result = deny_all_before(ctx)
expect(result.is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mdsoc/weaving_support_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MDSOC weaving support types
- deny advice

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
