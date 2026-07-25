# Inverted Index Specification

> <details>

<!-- sdn-diagram:id=inverted_index_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=inverted_index_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

inverted_index_spec -> std
inverted_index_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=inverted_index_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Inverted Index Specification

## Scenarios

### InvertedIndex build

#### indexes every doc and tracks the universe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = build_index()
expect(idx.doc_count()).to_equal(5)
```

</details>

#### distinct terms are interned once (dedup within a doc)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# corpus distinct terms: the,quick,brown,fox,lazy,dog,runs,jumps,cat = 9
val idx = build_index()
expect(idx.term_count()).to_equal(9)
```

</details>

### term lookup (absolute oracle)

#### returns the sorted doc-id set for a common term

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "the" appears in docs 1,2,4
val idx = build_index()
val r = ids_of(idx.postings_for("the"))
expect(r.len()).to_equal(3)
expect(r[0]).to_equal(1)
expect(r[1]).to_equal(2)
expect(r[2]).to_equal(4)
```

</details>

#### single-doc term yields a one-element posting

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "runs" appears only in doc 3
val idx = build_index()
val r = ids_of(idx.postings_for("runs"))
expect(r.len()).to_equal(1)
expect(r[0]).to_equal(3)
```

</details>

#### repeated term within a doc is deduped to one posting entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "lazy" -> docs 2 and 5 (doc 5 has it TWICE; must appear once)
val idx = build_index()
val r = ids_of(idx.postings_for("lazy"))
expect(r.len()).to_equal(2)
expect(r[0]).to_equal(2)
expect(r[1]).to_equal(5)
```

</details>

#### absent term returns an explicit empty posting (no sentinel)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = build_index()
val r = idx.postings_for("zebra")
expect(r.is_empty()).to_equal(true)
expect(r.len()).to_equal(0)
```

</details>

### Boolean AND (intersect)

#### matches the hand-computed oracle

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# quick: 1,3,4 ; brown: 1,3 ; AND -> 1,3
val idx = build_index()
val r = ids_of(idx.and_query("quick", "brown"))
expect(r.len()).to_equal(2)
expect(r[0]).to_equal(1)
expect(r[1]).to_equal(3)
```

</details>

#### agrees with independent brute-force contains scan

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = build_index()
val got = ids_of(idx.and_query("the", "quick"))
val oracle = brute_and("the", "quick")
expect(lists_equal(got, oracle)).to_equal(true)
# absolute: "the"={1,2,4}, "quick"={1,3,4} -> {1,4}
expect(got.len()).to_equal(2)
expect(got[0]).to_equal(1)
expect(got[1]).to_equal(4)
```

</details>

#### disjoint terms produce an empty result

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cat: 5 ; fox: 1,4 -> empty
val idx = build_index()
val r = idx.and_query("cat", "fox")
expect(r.is_empty()).to_equal(true)
```

</details>

### Boolean OR (union)

#### matches the hand-computed oracle, sorted + deduped

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# fox: 1,4 ; dog: 2,3 ; OR -> 1,2,3,4
val idx = build_index()
val r = ids_of(idx.or_query("fox", "dog"))
expect(r.len()).to_equal(4)
expect(r[0]).to_equal(1)
expect(r[1]).to_equal(2)
expect(r[2]).to_equal(3)
expect(r[3]).to_equal(4)
```

</details>

#### agrees with independent brute-force contains scan

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = build_index()
val got = ids_of(idx.or_query("brown", "lazy"))
val oracle = brute_or("brown", "lazy")
expect(lists_equal(got, oracle)).to_equal(true)
# absolute: brown={1,3}, lazy={2,5} -> {1,2,3,5}
expect(got.len()).to_equal(4)
expect(got[0]).to_equal(1)
expect(got[3]).to_equal(5)
```

</details>

### Boolean NOT (difference vs tracked universe)

#### returns universe minus the term's docs

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# universe={1,2,3,4,5}, "the"={1,2,4} -> {3,5}
val idx = build_index()
val r = ids_of(idx.not_query("the"))
expect(r.len()).to_equal(2)
expect(r[0]).to_equal(3)
expect(r[1]).to_equal(5)
```

</details>

#### NOT of an absent term is the whole universe

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = build_index()
val r = ids_of(idx.not_query("zebra"))
expect(r.len()).to_equal(5)
expect(r[0]).to_equal(1)
expect(r[4]).to_equal(5)
```

</details>

### phrase query (positional adjacency)

#### matches a phrase whose words are adjacent and in order

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "quick brown": adjacent in doc 1 (quick@1,brown@2) and doc 3
# (quick@0,brown@1). NOT doc 4 (quick@3, no brown).
val idx = build_index()
val r = ids_of(idx.phrase_query("quick", "brown"))
expect(r.len()).to_equal(2)
expect(r[0]).to_equal(1)
expect(r[1]).to_equal(3)
```

</details>

#### excludes docs where both words exist but are NOT adjacent

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# doc 4 = "the fox jumps quick": has BOTH "fox"(idx1) and "quick"(idx3)
# so AND matches it, but they are not adjacent in order -> phrase empty.
val idx = build_index()
val both = ids_of(idx.and_query("fox", "quick"))
# AND includes doc 4 (and doc 1: fox@3,quick@1)
expect(both).to_contain(4)
expect(both.len()).to_equal(2)
val phrase = idx.phrase_query("fox", "quick")
expect(phrase.is_empty()).to_equal(true)
```

</details>

#### order matters: brown quick is not a phrase here

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "quick brown" matches; reversed "brown quick" never adjacent-in-order
val idx = build_index()
val r = idx.phrase_query("brown", "quick")
expect(r.is_empty()).to_equal(true)
```

</details>

#### single-doc phrase: the quick (only doc 1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "the quick": doc1 the@0,quick@1 adjacent. doc2/doc4 have "the" but the
# next token is not "quick".
val idx = build_index()
val r = ids_of(idx.phrase_query("the", "quick"))
expect(r.len()).to_equal(1)
expect(r[0]).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/search/inverted_index_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- InvertedIndex build
- term lookup (absolute oracle)
- Boolean AND (intersect)
- Boolean OR (union)
- Boolean NOT (difference vs tracked universe)
- phrase query (positional adjacency)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
