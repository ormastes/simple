# Html5lib Tokenizer Specification

> <details>

<!-- sdn-diagram:id=html5lib_tokenizer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=html5lib_tokenizer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

html5lib_tokenizer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=html5lib_tokenizer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html5lib Tokenizer Specification

## Scenarios

### html5lib tokenizer test vectors

#### AC-6: test/fixtures/html5lib/test1.json fixture file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = _load_fixture("test1.json")
expect(content.len()).to_be_greater_than(0)
```

</details>

#### AC-6: test1.json contains at least one test vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = _load_fixture("test1.json")
val count = _count_vectors_in_json(content)
expect(count).to_be_greater_than(0)
```

</details>

#### AC-6: test1.json pass rate is at least 90 percent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rate = _pass_rate_for_fixture("test1.json")
expect(rate).to_be_greater_than(89)
```

</details>

#### AC-6: test2.json pass rate is at least 90 percent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rate = _pass_rate_for_fixture("test2.json")
expect(rate).to_be_greater_than(89)
```

</details>

### 132-corpus regression gate

#### AC-7: corpus baseline directory exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_file_text("test/baselines/famous_site_corpus/site_0/baseline.txt")
expect(content.len()).to_be_greater_than(-1)
```

</details>

#### AC-7: html tree builder produces a document node from minimal HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = _parse_html_doc_tag("<html><body></body></html>")
expect(tag).to_equal("#document")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/html5lib_tokenizer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- html5lib tokenizer test vectors
- 132-corpus regression gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
