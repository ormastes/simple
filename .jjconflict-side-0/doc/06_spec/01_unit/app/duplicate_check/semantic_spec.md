# Semantic Specification

> 1. signature: "fn add

<!-- sdn-diagram:id=semantic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=semantic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

semantic_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=semantic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Semantic Specification

## Scenarios

### doc_extractor

#### extracts fn with doc comment

1. signature: "fn add
   - Expected: entry.item_name equals `add`
   - Expected: entry.item_kind equals `fn`
   - Expected: entry.has_doc is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = DocEntry(
    file_path: "test.spl",
    line_number: 3,
    item_name: "add",
    item_kind: "fn",
    signature: "fn add(a: i64, b: i64) -> i64",
    doc_comment: "Add two numbers together",
    has_doc: true
)
expect(entry.item_name).to_equal("add")
expect(entry.item_kind).to_equal("fn")
expect(entry.has_doc).to_equal(true)
```

</details>

#### extracts fn without doc

1. signature: "fn helper
   - Expected: entry.has_doc is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = DocEntry(
    file_path: "test.spl",
    line_number: 5,
    item_name: "helper",
    item_kind: "fn",
    signature: "fn helper()",
    doc_comment: "",
    has_doc: false
)
expect(entry.has_doc).to_equal(false)
```

</details>

#### processes doc text - strips hash prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = process_doc_text("# This is a comment")
expect(result).to_equal("This is a comment")
```

</details>

#### processes doc text - strips multiple hashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = process_doc_text("## Section header")
expect(result).to_equal("Section header")
```

</details>

#### builds embedding key with doc

1. signature: "fn foo


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = DocEntry(
    file_path: "test.spl",
    line_number: 1,
    item_name: "foo",
    item_kind: "fn",
    signature: "fn foo(x: i64)",
    doc_comment: "Does something",
    has_doc: true
)
val key = build_embedding_key(entry)
expect(key).to_contain("fn foo")
expect(key).to_contain("Does something")
```

</details>

#### builds embedding key without doc

1. signature: "fn bar
   - Expected: key equals `fn bar()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = DocEntry(
    file_path: "test.spl",
    line_number: 1,
    item_name: "bar",
    item_kind: "fn",
    signature: "fn bar()",
    doc_comment: "",
    has_doc: false
)
val key = build_embedding_key(entry)
expect(key).to_equal("fn bar()")
```

</details>

#### content hash is deterministic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = content_hash("hello world")
val h2 = content_hash("hello world")
expect(h1).to_equal(h2)
```

</details>

#### content hash differs for different inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = content_hash("hello")
val h2 = content_hash("world")
val same = h1 == h2
expect(same).to_equal(false)
```

</details>

### ollama_client

#### parses float safely - positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = parse_float_safe("3.14")
val close = f > 3.13 and f < 3.15
expect(close).to_equal(true)
```

</details>

#### parses float safely - negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = parse_float_safe("-2.5")
val close = f > -2.6 and f < -2.4
expect(close).to_equal(true)
```

</details>

#### parses float safely - integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = parse_float_safe("42")
val close = f > 41.9 and f < 42.1
expect(close).to_equal(true)
```

</details>

#### parses float safely - zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = parse_float_safe("0.0")
val is_zero = f == 0.0
expect(is_zero).to_equal(true)
```

</details>

#### parses float safely - empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = parse_float_safe("")
val is_zero = f == 0.0
expect(is_zero).to_equal(true)
```

</details>

#### parses embedding response with embeddings key

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lb = (123 as char).to_text()
val rb = (125 as char).to_text()
val json = lb + "\"embeddings\":[[0.1,0.2,0.3]]" + rb
val values = parse_embedding_response(json)
expect(values.len()).to_equal(3)
```

</details>

#### parses embedding response - empty returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = parse_embedding_response("")
expect(values.len()).to_equal(0)
```

</details>

### embedding_cache

#### csv_to_floats converts comma-separated values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = csv_to_floats("1.0,2.5,3.7")
expect(result.len()).to_equal(3)
```

</details>

#### csv_to_floats handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = csv_to_floats("")
expect(result.len()).to_equal(0)
```

</details>

#### floats_to_csv converts array to csv

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val csv = floats_to_csv([1.0, 2.0, 3.0])
expect(csv).to_contain(",")
```

</details>

#### csv roundtrip preserves length

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = [0.1, 0.2, 0.3, 0.4]
val csv = floats_to_csv(original)
val restored = csv_to_floats(csv)
expect(restored.len()).to_equal(4)
```

</details>

#### cache starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = EmbeddingCacheManager(
    entries: {},
    cache_path: "/tmp/test_cache.txt",
    model_name: "test-model",
    hits: 0,
    misses: 0
)
val result = lookup_cached(cache, "key1", "hash1")
expect(result.embedding_csv).to_equal("")
expect(result.hit).to_equal(false)
```

</details>

#### set and get cached entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = EmbeddingCacheManager(
    entries: {},
    cache_path: "/tmp/test_cache.txt",
    model_name: "test-model",
    hits: 0,
    misses: 0
)
val cache2 = set_cached(cache, "key1", "hash1", "0.1,0.2,0.3")
val result = lookup_cached(cache2, "key1", "hash1")
expect(result.embedding_csv).to_equal("0.1,0.2,0.3")
expect(result.hit).to_equal(true)
```

</details>

#### cache miss on hash mismatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = EmbeddingCacheManager(
    entries: {},
    cache_path: "/tmp/test_cache.txt",
    model_name: "test-model",
    hits: 0,
    misses: 0
)
val cache2 = set_cached(cache, "key1", "hash1", "0.1,0.2,0.3")
val result = get_cached(cache2, "key1", "hash2")
expect(result).to_equal("")
```

</details>

### semantic - cosine similarity

#### identical vectors have similarity 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1.0, 0.0, 0.0]
val b = [1.0, 0.0, 0.0]
val sim = cosine_similarity_dense(a, b)
val close = sim > 0.99 and sim <= 1.0
expect(close).to_equal(true)
```

</details>

#### orthogonal vectors have similarity 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1.0, 0.0, 0.0]
val b = [0.0, 1.0, 0.0]
val sim = cosine_similarity_dense(a, b)
val close = sim >= 0.0 and sim < 0.01
expect(close).to_equal(true)
```

</details>

#### similar vectors have high similarity

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1.0, 1.0, 0.0]
val b = [1.0, 0.9, 0.1]
val sim = cosine_similarity_dense(a, b)
val high = sim > 0.9
expect(high).to_equal(true)
```

</details>

#### empty vectors return 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sim = cosine_similarity_dense([], [])
val is_zero = sim == 0.0
expect(is_zero).to_equal(true)
```

</details>

#### mismatched lengths return 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1.0, 2.0]
val b = [1.0, 2.0, 3.0]
val sim = cosine_similarity_dense(a, b)
val is_zero = sim == 0.0
expect(is_zero).to_equal(true)
```

</details>

### semantic - text similarity

#### identical strings have similarity 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sim = text_similarity("hello world", "hello world")
val is_one = sim == 1.0
expect(is_one).to_equal(true)
```

</details>

#### completely different strings have low similarity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sim = text_similarity("aaaaaa", "zzzzzz")
val is_low = sim < 0.5
expect(is_low).to_equal(true)
```

</details>

#### similar strings have high similarity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sim = text_similarity("add element to array", "add item to array")
val is_high = sim > 0.7
expect(is_high).to_equal(true)
```

</details>

### semantic - entrypoint extraction

#### extracts documented items through semantic analysis

1. var config = default config
   - Expected: report.total_items > 0 is true
   - Expected: report.items_with_docs > 0 is true
   - Expected: report.used_fallback is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = default_config()
config.exclude_patterns = []
config.ollama_url = "http://127.0.0.1:9"
config.semantic_threshold = 0.70

val report = run_semantic_analysis("test/fixtures/duplicate_check/semantic_supported_items.spl", config)

expect(report.total_items > 0).to_equal(true)
expect(report.items_with_docs > 0).to_equal(true)
expect(report.used_fallback).to_equal(true)
```

</details>

### semantic_formatter

#### severity_label for copy_paste

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val label = severity_label(0.98, "copy_paste")
expect(label).to_equal("[COPY-PASTE]")
```

</details>

#### severity_label for drift

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val label = severity_label(0.30, "drift")
expect(label).to_equal("[DRIFT]")
```

</details>

#### severity_label for similar high score

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val label = severity_label(0.96, "similar")
expect(label).to_equal("[NEAR-IDENTICAL]")
```

</details>

#### severity_label for similar lower score

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val label = severity_label(0.91, "similar")
expect(label).to_equal("[SIMILAR]")
```

</details>

#### format_match_line contains file paths

1. signature: "fn push
2. signature: "fn append


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry_a = DocEntry(
    file_path: "src/lib/array.spl",
    line_number: 45,
    item_name: "push",
    item_kind: "fn",
    signature: "fn push(arr, item)",
    doc_comment: "Add element to array",
    has_doc: true
)
val entry_b = DocEntry(
    file_path: "src/lib/array.spl",
    line_number: 89,
    item_name: "append",
    item_kind: "fn",
    signature: "fn append(arr, item)",
    doc_comment: "Append element to array",
    has_doc: true
)
val m = SemanticMatch(
    entry_a: entry_a,
    entry_b: entry_b,
    similarity: 0.95,
    match_kind: "similar"
)
val line = format_match_line(m)
expect(line).to_contain("src/lib/array.spl")
expect(line).to_contain("push")
expect(line).to_contain("append")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/duplicate_check/semantic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- doc_extractor
- ollama_client
- embedding_cache
- semantic - cosine similarity
- semantic - text similarity
- semantic - entrypoint extraction
- semantic_formatter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
