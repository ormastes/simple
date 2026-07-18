# Completion Specification

> 1. expect completion item kind number

<!-- sdn-diagram:id=completion_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=completion_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

completion_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=completion_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Completion Specification

## Scenarios

### CompletionItemKind

#### has Text kind

1. expect completion item kind number


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect completion_item_kind_number(CompletionItemKind.Text) == 1
```

</details>

#### has Method kind

1. expect completion item kind number


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect completion_item_kind_number(CompletionItemKind.Method) == 2
```

</details>

#### has Function kind

1. expect completion item kind number


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect completion_item_kind_number(CompletionItemKind.Function) == 3
```

</details>

#### has Variable kind

1. expect completion item kind number


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect completion_item_kind_number(CompletionItemKind.Variable) == 6
```

</details>

#### has Keyword kind

1. expect completion item kind number


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect completion_item_kind_number(CompletionItemKind.Keyword) == 14
```

</details>

#### has Struct kind

1. expect completion item kind number


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect completion_item_kind_number(CompletionItemKind.Struct) == 22
```

</details>

### CompletionItem

#### creates item with label and kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = CompletionItem.new("test", CompletionItemKind.Variable)
expect item.label == "test"
expect item.kind == CompletionItemKind.Variable
```

</details>

#### adds detail

1.  with detail
2. expect item detail == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = CompletionItem.new("fn", CompletionItemKind.Keyword)
    .with_detail("Function keyword")
expect item.detail == Some("Function keyword")
```

</details>

#### adds documentation

1.  with documentation
2. expect item documentation == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = CompletionItem.new("fn", CompletionItemKind.Keyword)
    .with_documentation("Define a function")
expect item.documentation == Some("Define a function")
```

</details>

#### adds insert text

1.  with insert text


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = CompletionItem.new("fn", CompletionItemKind.Snippet)
    .with_insert_text("fn ${1:name}():\n    ${0}")
expect item.insert_text != nil
```

</details>

#### chains builder methods

1.  with detail
2.  with documentation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = CompletionItem.new("struct", CompletionItemKind.Keyword)
    .with_detail("Define a struct")
    .with_documentation("Struct definitions create custom types")
expect item.detail != nil
expect item.documentation != nil
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lsp/completion_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CompletionItemKind
- CompletionItem

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
