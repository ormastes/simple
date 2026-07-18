# Semantic Tokens Specification

> 1. handler add token

<!-- sdn-diagram:id=semantic_tokens_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=semantic_tokens_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

semantic_tokens_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=semantic_tokens_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Semantic Tokens Specification

## Scenarios

### Semantic Tokens Handler

#### tokenizes keywords

1. handler add token
2. handler add token
3. var tokens = handler get tokens
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = MockSemanticTokenHandler.new()
handler.add_token(SemanticToken.new("keyword", 0, 0, 3))  # val
handler.add_token(SemanticToken.new("keyword", 0, 8, 2))  # fn
var tokens = handler.get_tokens()
check(tokens.len() == 2)
```

</details>

#### tokenizes identifiers

1. handler add token
2. handler add token
3. var tokens = handler get tokens
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = MockSemanticTokenHandler.new()
handler.add_token(SemanticToken.new("variable", 0, 4, 1))  # x
handler.add_token(SemanticToken.new("function", 0, 8, 6))  # my_func
var tokens = handler.get_tokens()
check(tokens.len() == 2)
```

</details>

#### tokenizes functions

1. handler add token
2. var tokens = handler get tokens
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = MockSemanticTokenHandler.new()
handler.add_token(SemanticToken.new("function", 1, 0, 10))  # my_function
var tokens = handler.get_tokens()
check(tokens.len() == 1)
```

</details>

#### tokenizes types

1. handler add token
2. handler add token
3. var tokens = handler get tokens
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = MockSemanticTokenHandler.new()
handler.add_token(SemanticToken.new("type", 0, 8, 3))  # i64
handler.add_token(SemanticToken.new("type", 0, 16, 4))  # List
var tokens = handler.get_tokens()
check(tokens.len() == 2)
```

</details>

#### tokenizes comments

1. handler add token
2. var tokens = handler get tokens
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = MockSemanticTokenHandler.new()
handler.add_token(SemanticToken.new("comment", 0, 0, 15))  # # This is comment
var tokens = handler.get_tokens()
check(tokens.len() == 1)
```

</details>

#### encodes delta positions

1. handler add token
2. handler add token
3. handler add token
4. var tokens = handler get tokens
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = MockSemanticTokenHandler.new()
handler.add_token(SemanticToken.new("keyword", 0, 0, 3))
handler.add_token(SemanticToken.new("variable", 0, 4, 1))
handler.add_token(SemanticToken.new("operator", 1, 2, 1))
var tokens = handler.get_tokens()
check(tokens.len() == 3)
```

</details>

#### includes visibility modifiers in the legend

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val legend = get_visibility_token_modifiers_legend()
check(legend.len() >= 12)
check(legend.contains("simple.visibility.public"))
check(legend.contains("simple.visibility.boundary"))
check(legend.contains("simple.visibility.private"))
```

</details>

#### maps visibility kinds to semantic token modifiers

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(visibility_modifier_for("public") == "simple.visibility.public")
check(visibility_modifier_for("boundary") == "simple.visibility.boundary")
check(visibility_modifier_for("private") == "simple.visibility.private")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lsp/semantic_tokens_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Semantic Tokens Handler

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
