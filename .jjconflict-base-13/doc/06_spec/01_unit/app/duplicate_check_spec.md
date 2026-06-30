# Duplicate Check Specification

> <details>

<!-- sdn-diagram:id=duplicate_check_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=duplicate_check_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

duplicate_check_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=duplicate_check_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Duplicate Check Specification

## Scenarios

### duplicate-check config

#### loads semantic-first defaults while keeping token mode available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_config()
expect(config.use_semantic).to_equal(true)
expect(config.use_cosine_similarity).to_equal(false)
expect(config.min_tokens).to_equal(30)
expect(config.min_lines).to_equal(5)
```

</details>

### duplicate-check tokenizer

#### tokenizes simple code

1. var config = default config
   - Expected: tokens[0].value equals `fn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = default_config()
config.use_semantic = false
config.ignore_identifiers = false
val source = "fn test(value: i64) -> i64:\n    value + 1\n"
val tokens = tokenize(source, config)
expect(tokens.len()).to_be_greater_than(0)
expect(tokens[0].value).to_equal("fn")
```

</details>

#### normalizes identifiers when configured

1. var config = default config
   - Expected: has_identifier_token is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = default_config()
config.use_semantic = false
config.ignore_identifiers = true
val source = "var count = total + 1"
val tokens = tokenize(source, config)
var has_identifier_token = false
for token in tokens:
    if token.kind == SimpleTokenKind.Identifier and token.value == "IDENTIFIER":
        has_identifier_token = true
expect(has_identifier_token).to_equal(true)
```

</details>

### duplicate-check file collection

#### collects fixture files from directory

1. var config = default config


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = default_config()
config.use_semantic = false
config.exclude_patterns = []
val files = collect_files(fixture_root(), config)
expect(files.len()).to_be_greater_than(3)
```

</details>

#### excludes files by pattern

1. var config = default config
   - Expected: has_doc_fixture is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = default_config()
config.use_semantic = false
config.exclude_patterns = ["doc_fixture"]
val files = collect_files(fixture_root(), config)
var has_doc_fixture = false
for file in files:
    if file.contains("doc_fixture"):
        has_doc_fixture = true
expect(has_doc_fixture).to_equal(false)
```

</details>

### duplicate-check features

#### extracts token frequencies

1. SimpleToken
2. SimpleToken
3. SimpleToken
   - Expected: freq_map["SimpleTokenKind::Keyword:fn"] equals `1`
   - Expected: freq_map["SimpleTokenKind::Identifier:test"] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = [
    SimpleToken(kind: SimpleTokenKind.Keyword, value: "fn", line: 1, column: 1, start_offset: 0, end_offset: 2),
    SimpleToken(kind: SimpleTokenKind.Identifier, value: "test", line: 1, column: 4, start_offset: 3, end_offset: 7),
    SimpleToken(kind: SimpleTokenKind.Identifier, value: "test", line: 1, column: 9, start_offset: 8, end_offset: 12)
]

val freq_map = extract_token_frequencies(tokens, 0, 3)
expect(freq_map["SimpleTokenKind::Keyword:fn"]).to_equal(1)
expect(freq_map["SimpleTokenKind::Identifier:test"]).to_equal(2)
```

</details>

#### computes cosine similarity for identical vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var freq_map = {}
freq_map["SimpleTokenKind::Keyword:fn"] = 1
freq_map["SimpleTokenKind::Identifier:test"] = 2

val vector1 = build_feature_vector(0, freq_map)
val vector2 = build_feature_vector(1, freq_map)
val similarity = cosine_similarity(vector1, vector2)

expect(similarity).to_be_greater_than(0.99)
```

</details>

#### computes cosine similarity for different vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var freq_map1 = {}
freq_map1["SimpleTokenKind::Keyword:fn"] = 1
freq_map1["SimpleTokenKind::Identifier:test"] = 2

var freq_map2 = {}
freq_map2["SimpleTokenKind::Keyword:var"] = 1
freq_map2["SimpleTokenKind::Identifier:count"] = 1

val vector1 = build_feature_vector(0, freq_map1)
val vector2 = build_feature_vector(1, freq_map2)
val similarity = cosine_similarity(vector1, vector2)

expect(similarity).to_be_less_than(1.0)
```

</details>

### duplicate-check semantic fallback

#### detects similar docs without ollama

1. signature: "fn sum values
2. signature: "fn sum numbers
   - Expected: report.matches.len() equals `1`
   - Expected: report.matches[0].match_kind contains `text-based`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = [
    DocEntry(
        file_path: "a.spl",
        line_number: 1,
        item_name: "sum_values",
        item_kind: "fn",
        signature: "fn sum_values(values: [i64]) -> i64",
        doc_comment: "Compute the total sum of all values in the input list and return the accumulated result.",
        has_doc: true
    ),
    DocEntry(
        file_path: "b.spl",
        line_number: 1,
        item_name: "sum_numbers",
        item_kind: "fn",
        signature: "fn sum_numbers(numbers: [i64]) -> i64",
        doc_comment: "Compute the total sum of all values in the input list and return the accumulated result.",
        has_doc: true
    )
]
val report = run_text_fallback(entries, 0.90, 0.40)
expect(report.matches.len()).to_equal(1)
expect(report.matches[0].match_kind.contains("text-based")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/duplicate_check_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- duplicate-check config
- duplicate-check tokenizer
- duplicate-check file collection
- duplicate-check features
- duplicate-check semantic fallback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
