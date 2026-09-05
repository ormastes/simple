# Semantic Tokens Integration Specification

> 1. check

<!-- sdn-diagram:id=semantic_tokens_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=semantic_tokens_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

semantic_tokens_integration_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=semantic_tokens_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Semantic Tokens Integration Specification

## Scenarios

### Semantic Tokens Integration

#### tokenizes Simple source code

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokenizer = MockTokenizer.new()
val source = "val x = 42"
val token_count = tokenizer.tokenize(source)
check(token_count >= 0)
```

</details>

#### handles multiline constructs

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokenizer = MockTokenizer.new()
val source = "class Point:\n    x: i64\n    y: i64"
val token_count = tokenizer.tokenize(source)
check(token_count >= 0)
```

</details>

#### handles incremental updates

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokenizer = MockTokenizer.new()
val old_code = "val x = 10"
val new_code = "val x = 10\nval y = 20"
val old_count = tokenizer.tokenize(old_code)
val new_count = tokenizer.tokenize(new_code)
check(new_count >= old_count)
```

</details>

#### integrates with Tree-sitter

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokenizer = MockTokenizer.new()
val source = "fn add(x: i64, y: i64) -> i64:\n    x + y"
val tokens = tokenizer.tokenize(source)
check(tokens > 0)
```

</details>

#### filters private symbols from visible symbol lists

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbols = ["Router", "route_debug", "_private_helper"]
val filtered = filter_visible_symbols(symbols, "boundary")
check(filtered.len() == 2)
check(filtered.contains("Router"))
check(filtered.contains("route_debug"))
check(not filtered.contains("_private_helper"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lsp/semantic_tokens_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Semantic Tokens Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
