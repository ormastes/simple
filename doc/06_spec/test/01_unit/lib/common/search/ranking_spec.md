# Ranking Specification

> <details>

<!-- sdn-diagram:id=ranking_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ranking_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ranking_spec -> std
ranking_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ranking_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ranking Specification

## Scenarios

### avg_doc_len_fixed

#### computes a fixed-point mean (6.0 -> 6_000_000)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(avg_doc_len_fixed([4, 6, 8])).to_equal(6000000)
```

</details>

#### keeps fractional averages in fixed-point (5/2 = 2.5 -> 2_500_000)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(avg_doc_len_fixed([2, 3])).to_equal(2500000)
```

</details>

#### is 0 for an empty corpus

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(avg_doc_len_fixed([])).to_equal(0)
```

</details>

### BM25 absolute-oracle scores (k1=1.2, b=0.75)

#### doc0 (cat x3, dog absent, dl=4) scores 795 milli

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# tfs aligned to query [cat, dog]; df aligned the same way.
val s = bm25_score_default([3, 0], [2, 2], 4, corpus_avgdl(), 3)
expect(milli_of(s)).to_equal(795)
```

</details>

#### doc1 (cat x1, dog x2, dl=6) scores 1116 milli

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = bm25_score_default([1, 2], [2, 2], 6, corpus_avgdl(), 3)
expect(milli_of(s)).to_equal(1116)
```

</details>

#### doc2 (cat absent, dog x2, dl=8) scores 590 milli

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = bm25_score_default([0, 2], [2, 2], 8, corpus_avgdl(), 3)
expect(milli_of(s)).to_equal(590)
```

</details>

#### a term absent in a doc contributes nothing (tf=0 term dropped)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# doc with only cat present must equal the same doc scored cat-only.
val both = bm25_score_default([3, 0], [2, 2], 4, corpus_avgdl(), 3)
val cat_only = bm25_score_default([3], [2], 4, corpus_avgdl(), 3)
expect(milli_of(both)).to_equal(milli_of(cat_only))
expect(milli_of(cat_only)).to_equal(795)
```

</details>

### TF-IDF absolute-oracle scores

#### tf=1, df=3, N=3 -> 133 milli (ln(8/7))

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = tfidf_score([1], [3], 3)
expect(milli_of(s)).to_equal(133)
```

</details>

#### tf=3, df=3, N=3 -> 400 milli (3 * ln(8/7))

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = tfidf_score([3], [3], 3)
expect(milli_of(s)).to_equal(400)
```

</details>

#### tf=0 contributes 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = tfidf_score([0], [3], 3)
expect(milli_of(s)).to_equal(0)
```

</details>

### ranking order over the hand corpus

#### ranks doc1 > doc0 > doc2 by BM25 score

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val avg = corpus_avgdl()
val d0 = ScoredDoc.of(0, bm25_score_default([3, 0], [2, 2], 4, avg, 3))
val d1 = ScoredDoc.of(1, bm25_score_default([1, 2], [2, 2], 6, avg, 3))
val d2 = ScoredDoc.of(2, bm25_score_default([0, 2], [2, 2], 8, avg, 3))
val ranked = rank_all([d0, d1, d2])
expect(ranked.len()).to_equal(3)
expect(ranked[0].doc_id()).to_equal(1)
expect(ranked[1].doc_id()).to_equal(0)
expect(ranked[2].doc_id()).to_equal(2)
# exact scaled scores survive into the ranked output
expect(milli_of(ranked[0].relevance())).to_equal(1116)
expect(milli_of(ranked[1].relevance())).to_equal(795)
expect(milli_of(ranked[2].relevance())).to_equal(590)
```

</details>

### top_k selection over Score

#### returns the k best in ranked order

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = ScoredDoc.of(10, Score.from_milli(500))
val b = ScoredDoc.of(11, Score.from_milli(900))
val c = ScoredDoc.of(12, Score.from_milli(700))
val d = ScoredDoc.of(13, Score.from_milli(300))
val r = top_k([a, b, c, d], 2)
expect(r.len()).to_equal(2)
expect(r[0].doc_id()).to_equal(11)
expect(r[1].doc_id()).to_equal(12)
```

</details>

#### breaks ties by ascending id (deterministic, no stability reliance)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# three docs share score 700; ids 5, 2, 9 must come out 2, 5, 9.
val x = ScoredDoc.of(5, Score.from_milli(700))
val y = ScoredDoc.of(2, Score.from_milli(700))
val z = ScoredDoc.of(9, Score.from_milli(700))
val r = top_k([x, y, z], 3)
expect(r.len()).to_equal(3)
expect(r[0].doc_id()).to_equal(2)
expect(r[1].doc_id()).to_equal(5)
expect(r[2].doc_id()).to_equal(9)
```

</details>

#### mixed tie and ordering: top score wins, then id tie-break

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = ScoredDoc.of(8, Score.from_milli(900))
val q = ScoredDoc.of(3, Score.from_milli(900))
val rr = ScoredDoc.of(1, Score.from_milli(400))
val r = top_k([p, q, rr], 3)
expect(r[0].doc_id()).to_equal(3)
expect(r[1].doc_id()).to_equal(8)
expect(r[2].doc_id()).to_equal(1)
```

</details>

#### k larger than corpus returns all, k=0 returns none

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = ScoredDoc.of(1, Score.from_milli(100))
val b = ScoredDoc.of(2, Score.from_milli(200))
expect(top_k([a, b], 9).len()).to_equal(2)
expect(top_k([a, b], 0).len()).to_equal(0)
expect(top_k([], 3).len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/search/ranking_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- avg_doc_len_fixed
- BM25 absolute-oracle scores (k1=1.2, b=0.75)
- TF-IDF absolute-oracle scores
- ranking order over the hand corpus
- top_k selection over Score

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
