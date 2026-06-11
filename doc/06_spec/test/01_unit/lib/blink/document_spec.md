# Blink Document Specification

> Tests for the Blink-style Document stub — the root DOM container that owns a DomTree, tracks the document URL, title, and HTML5 ready-state lifecycle (Loading -> Interactive -> Complete).

<!-- sdn-diagram:id=document_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=document_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

document_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=document_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink Document Specification

Tests for the Blink-style Document stub — the root DOM container that owns a DomTree, tracks the document URL, title, and HTML5 ready-state lifecycle (Loading -> Interactive -> Complete).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Stub |
| Source | `test/01_unit/lib/blink/document_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the Blink-style Document stub — the root DOM container that
owns a DomTree, tracks the document URL, title, and HTML5 ready-state
lifecycle (Loading -> Interactive -> Complete).

## Scenarios

### document_new

#### ready_state is Loading, character_set is UTF-8

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = document_new("http://example.com/")
val is_loading = doc.ready_state == ReadyState.Loading
expect(is_loading).to_equal(true)
expect(doc.character_set).to_equal("UTF-8")
expect(doc.content_type).to_equal("text/html")
```

</details>

#### url is parsed from input string

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = document_new("https://www.example.com/path?q=1")
expect(doc.url.scheme).to_equal("https")
expect(doc.url.host).to_equal("www.example.com")
expect(doc.url.is_valid).to_equal(true)
```

</details>

### set_title

#### updates title field

1. doc set title
   - Expected: doc.title equals `Hello World`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = document_new("http://example.com/")
doc.set_title("Hello World")
expect(doc.title).to_equal("Hello World")
```

</details>

### set_ready_state

#### updates state

1. doc set ready state
   - Expected: is_interactive is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = document_new("http://example.com/")
doc.set_ready_state(ReadyState.Interactive)
val is_interactive = doc.ready_state == ReadyState.Interactive
expect(is_interactive).to_equal(true)
```

</details>

### create_element

#### returns new node id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = document_new("http://example.com/")
val div_id = doc.create_element("div")
expect(div_id).to_be_greater_than(0)
```

</details>

### is_loading

#### returns true initially, false after set_ready_state(Complete)

1. doc set ready state
   - Expected: doc.is_loading() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = document_new("http://example.com/")
expect(doc.is_loading()).to_equal(true)
doc.set_ready_state(ReadyState.Complete)
expect(doc.is_loading()).to_equal(false)
```

</details>

### is_complete

#### returns true only when ready_state is Complete

1. doc set ready state
   - Expected: doc.is_complete() is false
2. doc set ready state
   - Expected: doc.is_complete() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = document_new("http://example.com/")
expect(doc.is_complete()).to_equal(false)
doc.set_ready_state(ReadyState.Interactive)
expect(doc.is_complete()).to_equal(false)
doc.set_ready_state(ReadyState.Complete)
expect(doc.is_complete()).to_equal(true)
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
