# fts_engine_spec

> FTS Engine Specification

<!-- sdn-diagram:id=fts_engine_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fts_engine_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fts_engine_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fts_engine_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fts_engine_spec

FTS Engine Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/fts_engine_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

FTS Engine Specification

Verifies full-text search engine components:
  - Tokenizer: tokenization, stop words, positions
  - Inverted index: indexing, search, removal
  - BM25: scoring and ranking
  - Trigram: trigram generation, substring search
  - Fuzzy: Levenshtein distance, fuzzy matching
  - FtsEngine: unified search API

## Scenarios

### FTS Tokenizer

#### tokenizes simple text into lowercase terms

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = fts_tokenize("Hello World")
expect(tokens.len()).to_equal(2)
expect(tokens[0].term).to_equal("hello")
expect(tokens[1].term).to_equal("world")
```

</details>

#### filters stop words

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = fts_tokenize("the quick brown fox is in the house")
# "the", "is", "in", "the" are stop words -> removed
# remaining: quick, brown, fox, house
expect(tokens.len()).to_equal(4)
expect(tokens[0].term).to_equal("quick")
expect(tokens[1].term).to_equal("brown")
expect(tokens[2].term).to_equal("fox")
expect(tokens[3].term).to_equal("house")
```

</details>

#### tracks positions after stop word removal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = fts_tokenize("Hello World")
expect(tokens[0].position).to_equal(0)
expect(tokens[1].position).to_equal(1)
```

</details>

#### raw tokenize preserves stop words

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = fts_tokenize_raw("the quick fox")
expect(raw.len()).to_equal(3)
expect(raw[0]).to_equal("the")
```

</details>

#### splits on punctuation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = fts_tokenize_raw("hello,world.test")
expect(tokens.len()).to_equal(3)
expect(tokens[0]).to_equal("hello")
expect(tokens[1]).to_equal("world")
expect(tokens[2]).to_equal("test")
```

</details>

### FTS Inverted Index

#### indexes a document and finds terms

1. var idx = FtsInvertedIndex new
2. idx index document
   - Expected: results.len() equals `1`
   - Expected: first.doc_id equals `1`
   - Expected: first.term_freq equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var idx = FtsInvertedIndex.new()
idx.index_document(1, "hello world hello")
val results = idx.search("hello")
expect(results.len()).to_equal(1)
val first = results[0]
expect(first.doc_id).to_equal(1)
expect(first.term_freq).to_equal(2)
```

</details>

#### tracks document count

1. var idx = FtsInvertedIndex new
2. idx index document
3. idx index document
   - Expected: idx.doc_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var idx = FtsInvertedIndex.new()
idx.index_document(1, "hello world")
idx.index_document(2, "world test")
expect(idx.doc_count()).to_equal(2)
```

</details>

#### returns empty for unknown terms

1. var idx = FtsInvertedIndex new
2. idx index document
   - Expected: results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var idx = FtsInvertedIndex.new()
idx.index_document(1, "hello world")
val results = idx.search("unknown")
expect(results.len()).to_equal(0)
```

</details>

#### removes a document from index

1. var idx = FtsInvertedIndex new
2. idx index document
3. idx index document
4. idx remove document
   - Expected: idx.doc_count() equals `1`
   - Expected: rlen equals `1`
   - Expected: first.doc_id equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var idx = FtsInvertedIndex.new()
idx.index_document(1, "hello world")
idx.index_document(2, "hello test")
idx.remove_document(1)
expect(idx.doc_count()).to_equal(1)
val results = idx.search("hello")
val rlen = results.len() as i64
expect(rlen).to_equal(1)
val first = results[0]
expect(first.doc_id).to_equal(2)
```

</details>

#### reports doc_freq correctly

1. var idx = FtsInvertedIndex new
2. idx index document
3. idx index document
   - Expected: idx.doc_freq("hello") equals `2`
   - Expected: idx.doc_freq("world") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var idx = FtsInvertedIndex.new()
idx.index_document(1, "hello world")
idx.index_document(2, "hello test")
expect(idx.doc_freq("hello")).to_equal(2)
expect(idx.doc_freq("world")).to_equal(1)
```

</details>

### FTS BM25 Scoring

#### produces non-zero score for matching terms

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sc = fts_bm25_score(2, 1, 5, 5, 10)
expect(sc > 0).to_equal(true)
```

</details>

#### scores zero when tf is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sc = fts_bm25_score(0, 1, 5, 5, 10)
expect(sc).to_equal(0)
```

</details>

#### ranks documents by relevance

1. var idx = FtsInvertedIndex new
2. idx index document
3. idx index document
4. idx index document
   - Expected: rlen > 0 is true
   - Expected: first.doc_id equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var idx = FtsInvertedIndex.new()
idx.index_document(1, "simple simple simple database")
idx.index_document(2, "simple query")
idx.index_document(3, "complex database system")
val results = fts_bm25_search(idx, "simple")
val rlen = results.len() as i64
expect(rlen > 0).to_equal(true)
val first = results[0]
expect(first.doc_id).to_equal(1)
```

</details>

### FTS Trigram Index

#### generates trigrams from text

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tris = fts_generate_trigrams("hello")
# "hel", "ell", "llo"
expect(tris.len()).to_equal(3)
expect(tris[0]).to_equal("hel")
expect(tris[1]).to_equal("ell")
expect(tris[2]).to_equal("llo")
```

</details>

#### returns empty for short text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tris = fts_generate_trigrams("ab")
expect(tris.len()).to_equal(0)
```

</details>

#### finds documents by substring

1. var tri = FtsTrigramIndex new
2. tri index document
3. tri index document
   - Expected: results.len() equals `1`
   - Expected: results[0] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tri = FtsTrigramIndex.new()
tri.index_document(1, "hello world")
tri.index_document(2, "goodbye world")
val results = tri.search("hello")
expect(results.len()).to_equal(1)
expect(results[0]).to_equal(1)
```

</details>

#### finds documents matching all trigrams

1. var tri = FtsTrigramIndex new
2. tri index document
3. tri index document
   - Expected: results.len() equals `1`
   - Expected: results[0] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tri = FtsTrigramIndex.new()
tri.index_document(1, "hello world")
tri.index_document(2, "hello there")
val results = tri.search("world")
expect(results.len()).to_equal(1)
expect(results[0]).to_equal(1)
```

</details>

#### removes a document from trigram index

1. var tri = FtsTrigramIndex new
2. tri index document
3. tri remove document
   - Expected: results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tri = FtsTrigramIndex.new()
tri.index_document(1, "hello world")
tri.remove_document(1)
val results = tri.search("hello")
expect(results.len()).to_equal(0)
```

</details>

### FTS Fuzzy Search

#### computes zero distance for identical strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fts_levenshtein("hello", "hello")).to_equal(0)
```

</details>

#### computes distance 1 for single edit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fts_levenshtein("hello", "helo")).to_equal(1)
```

</details>

#### computes distance for substitution

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fts_levenshtein("cat", "bat")).to_equal(1)
```

</details>

#### computes distance for insertion

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fts_levenshtein("cat", "cats")).to_equal(1)
```

</details>

#### handles empty strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fts_levenshtein("", "abc")).to_equal(3)
expect(fts_levenshtein("abc", "")).to_equal(3)
```

</details>

#### fuzzy matches within distance threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates: [text] = ["hello", "helo", "world", "help", "hallo"]
val matches = fts_fuzzy_match("hello", candidates, 1)
expect(matches.len()).to_equal(3)
```

</details>

### FTS Engine

#### adds documents and searches by keyword

1. var engine = FtsEngine new
2. engine add document
3. engine add document
   - Expected: rlen equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = FtsEngine.new()
engine.add_document(1, "quick brown fox jumps over lazy dog")
engine.add_document(2, "slow red fox sleeps under tree")
val results = engine.search_keyword("fox")
val rlen = results.len() as i64
expect(rlen).to_equal(2)
```

</details>

#### searches by substring

1. var engine = FtsEngine new
2. engine add document
3. engine add document
   - Expected: results.len() equals `1`
   - Expected: results[0] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = FtsEngine.new()
engine.add_document(1, "hello world testing")
engine.add_document(2, "goodbye world testing")
val results = engine.search_substring("hello")
expect(results.len()).to_equal(1)
expect(results[0]).to_equal(1)
```

</details>

#### combined search returns results

1. var engine = FtsEngine new
2. engine add document
3. engine add document
   - Expected: rlen > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = FtsEngine.new()
engine.add_document(1, "database query engine search")
engine.add_document(2, "simple text search tool")
val results = engine.search("search")
val rlen = results.len() as i64
expect(rlen > 0).to_equal(true)
```

</details>

#### removes document from engine

1. var engine = FtsEngine new
2. engine add document
3. engine add document
4. engine remove document
   - Expected: rlen equals `1`
   - Expected: first.doc_id equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = FtsEngine.new()
engine.add_document(1, "hello world")
engine.add_document(2, "hello test")
engine.remove_document(1)
val kw_results = engine.search_keyword("hello")
val rlen = kw_results.len() as i64
expect(rlen).to_equal(1)
val first = kw_results[0]
expect(first.doc_id).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
