# ranking_spec

> Purpose: Prove that avg_doc_len_fixed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ranking_spec

Purpose: Prove that avg_doc_len_fixed.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/search/ranking_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that avg_doc_len_fixed.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### bm25-fixed-v1 checked arithmetic

#### matches the hand-computed term intermediate vector exactly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the hand-computed term intermediate vector exactly
- Verify the frozen integer operation-order vector
   - Expected: trace.average_length_scaled equals `6000000`
   - Expected: trace.ratio_scaled equals `1000000`
   - Expected: trace.norm_scaled equals `1000000`
   - Expected: trace.denominator_scaled equals `2200000`
   - Expected: trace.tf_scaled equals `1000000`
   - Expected: trace.idf_argument_scaled equals `1600000`
   - Expected: trace.idf_scaled equals `469998`
   - Expected: trace.unweighted equals `469998`
   - Expected: trace.weighted equals `469998`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the hand-computed term intermediate vector exactly")
step("Verify the frozen integer operation-order vector")
# Independent paper vector for tf=1, dl=6, total=18, N=3, df=2:
# avg=18*1e6/3=6000000; ratio=6*1e12/6000000=1000000;
# norm=250000+750000=1000000; denom=1000000+1200000;
# tf_scaled=1*2200000*1e6/2200000=1000000;
# idf_arg=1e6+(6-4+1)*1e6/(4+1)=1600000;
# seven-term fixed ln=469998; weighted at 1000 remains 469998.
val trace = bm25_fixed_v1_term_checked(1, 6, 18, 3, 2, 1000).unwrap()
expect(trace.average_length_scaled).to_equal(6000000)
expect(trace.ratio_scaled).to_equal(1000000)
expect(trace.norm_scaled).to_equal(1000000)
expect(trace.denominator_scaled).to_equal(2200000)
expect(trace.tf_scaled).to_equal(1000000)
expect(trace.idf_argument_scaled).to_equal(1600000)
expect(trace.idf_scaled).to_equal(469998)
expect(trace.unweighted).to_equal(469998)
expect(trace.weighted).to_equal(469998)
```

</details>

#### matches fixed-ln reduction boundary vectors

- matches fixed-ln reduction boundary vectors
- Verify hardcoded p13-series boundary results
   - Expected: fixed_ln_checked(1).unwrap() equals `0 - 13815508`
   - Expected: fixed_ln_checked(499999).unwrap() equals `0 - 693154`
   - Expected: fixed_ln_checked(500000).unwrap() equals `0 - 693147`
   - Expected: fixed_ln_checked(500001).unwrap() equals `0 - 693147`
   - Expected: fixed_ln_checked(999999).unwrap() equals `0 - 7`
   - Expected: fixed_ln_checked(1000000).unwrap() equals `0`
   - Expected: fixed_ln_checked(1000001).unwrap() equals `0`
   - Expected: fixed_ln_checked(1999999).unwrap() equals `693142`
   - Expected: fixed_ln_checked(2000000).unwrap() equals `693147`
   - Expected: fixed_ln_checked(2000001).unwrap() equals `693147`
   - Expected: fixed_ln_checked(9223372036854775807).unwrap() equals `29852751`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches fixed-ln reduction boundary vectors")
step("Verify hardcoded p13-series boundary results")
expect(fixed_ln_checked(1).unwrap()).to_equal(0 - 13815508)
expect(fixed_ln_checked(499999).unwrap()).to_equal(0 - 693154)
expect(fixed_ln_checked(500000).unwrap()).to_equal(0 - 693147)
expect(fixed_ln_checked(500001).unwrap()).to_equal(0 - 693147)
expect(fixed_ln_checked(999999).unwrap()).to_equal(0 - 7)
expect(fixed_ln_checked(1000000).unwrap()).to_equal(0)
expect(fixed_ln_checked(1000001).unwrap()).to_equal(0)
expect(fixed_ln_checked(1999999).unwrap()).to_equal(693142)
expect(fixed_ln_checked(2000000).unwrap()).to_equal(693147)
expect(fixed_ln_checked(2000001).unwrap()).to_equal(693147)
expect(fixed_ln_checked(9223372036854775807).unwrap()).to_equal(29852751)
```

</details>

#### accepts both document-frequency boundaries

- accepts both document-frequency boundaries
- Verify df zero and df equal to N use frozen nonnegative IDF
   - Expected: unseen.idf_argument_scaled equals `4000000`
   - Expected: unseen.idf_scaled equals `1386294`
   - Expected: universal.idf_argument_scaled equals `1333333`
   - Expected: universal.idf_scaled equals `287678`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts both document-frequency boundaries")
step("Verify df zero and df equal to N use frozen nonnegative IDF")
val unseen = bm25_fixed_v1_term_checked(1, 1, 1, 1, 0, 1000).unwrap()
val universal = bm25_fixed_v1_term_checked(1, 1, 1, 1, 1, 1000).unwrap()
expect(unseen.idf_argument_scaled).to_equal(4000000)
expect(unseen.idf_scaled).to_equal(1386294)
expect(universal.idf_argument_scaled).to_equal(1333333)
expect(universal.idf_scaled).to_equal(287678)
```

</details>

#### pins every truncating BM25 division stage

- pins every truncating BM25 division stage
- Verify average, ratio, norm, TF, IDF, unweighted, and field weight truncation
   - Expected: average_rounding.average_length_scaled equals `333333`
   - Expected: average_rounding.ratio_scaled equals `3000003`
   - Expected: average_rounding.norm_scaled equals `2500002`
   - Expected: average_rounding.denominator_scaled equals `4000002`
   - Expected: average_rounding.tf_scaled equals `549999`
   - Expected: average_rounding.idf_argument_scaled equals `2666666`
   - Expected: average_rounding.idf_scaled equals `980825`
   - Expected: average_rounding.unweighted equals `539452`
   - Expected: average_rounding.weighted equals `1078904`
   - Expected: weight_rounding.average_length_scaled equals `3000000`
   - Expected: weight_rounding.ratio_scaled equals `333333`
   - Expected: weight_rounding.norm_scaled equals `499999`
   - Expected: weight_rounding.denominator_scaled equals `1599998`
   - Expected: weight_rounding.tf_scaled equals `1375001`
   - Expected: weight_rounding.idf_scaled equals `1386294`
   - Expected: weight_rounding.unweighted equals `1906155`
   - Expected: weight_rounding.weighted equals `4765387`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pins every truncating BM25 division stage")
step("Verify average, ratio, norm, TF, IDF, unweighted, and field weight truncation")
# total*S/N truncates to 333333. Each following value is calculated
# independently from the frozen integer formula, never from a scorer.
val average_rounding = bm25_fixed_v1_term_checked(
    1, 1, 1, 3, 1, 2000).unwrap()
expect(average_rounding.average_length_scaled).to_equal(333333)
expect(average_rounding.ratio_scaled).to_equal(3000003)
expect(average_rounding.norm_scaled).to_equal(2500002)
expect(average_rounding.denominator_scaled).to_equal(4000002)
expect(average_rounding.tf_scaled).to_equal(549999)
expect(average_rounding.idf_argument_scaled).to_equal(2666666)
expect(average_rounding.idf_scaled).to_equal(980825)
expect(average_rounding.unweighted).to_equal(539452)
expect(average_rounding.weighted).to_equal(1078904)
# 1,906,155 * 2,500 / 1,000 = 4,765,387.5 -> 4,765,387.
val weight_rounding = bm25_fixed_v1_term_checked(
    1, 1, 3, 1, 0, 2500).unwrap()
expect(weight_rounding.average_length_scaled).to_equal(3000000)
expect(weight_rounding.ratio_scaled).to_equal(333333)
expect(weight_rounding.norm_scaled).to_equal(499999)
expect(weight_rounding.denominator_scaled).to_equal(1599998)
expect(weight_rounding.tf_scaled).to_equal(1375001)
expect(weight_rounding.idf_scaled).to_equal(1386294)
expect(weight_rounding.unweighted).to_equal(1906155)
expect(weight_rounding.weighted).to_equal(4765387)
```

</details>

#### accumulates fields before the sole final milli conversion

- accumulates fields before the sole final milli conversion
- Verify field-order accumulation does not round each field
   - Expected: milli_of(score) equals `3759`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accumulates fields before the sole final milli conversion")
step("Verify field-order accumulation does not round each field")
# Each official-weight-4000 field contributes internal 1,879,992.
# One final conversion is (1,879,992 + 1,879,992) / 1000 = 3,759.
# Per-field public conversion would incorrectly produce 3,758.
val identifier = Bm25FieldV1.of(
    "identifier", ["cat"], [1], [2], 6, 18, 3)
val title = Bm25FieldV1.of(
    "title", ["cat"], [1], [2], 6, 18, 3)
val score = bm25_fixed_v1_score_checked([identifier, title]).unwrap()
expect(milli_of(score)).to_equal(3759)
```

</details>

#### scores each distinct ordered term once and rejects duplicates

- scores each distinct ordered term once and rejects duplicates
- Verify the pre-deduplicated query-term boundary
   - Expected: bm25_fixed_v1_score_checked([unique]).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("scores each distinct ordered term once and rejects duplicates")
step("Verify the pre-deduplicated query-term boundary")
val unique = Bm25FieldV1.of(
    "body", ["cat", "dog"], [1, 2], [2, 2], 6, 18, 3)
expect(bm25_fixed_v1_score_checked([unique]).is_ok()).to_equal(true)
val duplicate = Bm25FieldV1.of(
    "body", ["cat", "cat"], [1, 1], [2, 2], 6, 18, 3)
expect(bm25_fixed_v1_score_checked([duplicate]).unwrap_err()).to_equal(
    "invalid_parallel_arrays")
val reversed = Bm25FieldV1.of(
    "body", ["dog", "cat"], [2, 1], [2, 2], 6, 18, 3)
expect(bm25_fixed_v1_score_checked([reversed]).unwrap_err()).to_equal(
    "invalid_parallel_arrays")
```

</details>

#### keeps absent terms at zero without evaluating invalid divisions

- keeps absent terms at zero without evaluating invalid divisions
- Verify tf zero bypasses average and denominator evaluation
   - Expected: direct.average_length_scaled equals `0`
   - Expected: direct.idf_argument_scaled equals `0`
   - Expected: direct.denominator_scaled equals `0`
   - Expected: direct.weighted equals `0`
   - Expected: milli_of(bm25_fixed_v1_score_checked([absent]).unwrap()) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps absent terms at zero without evaluating invalid divisions")
step("Verify tf zero bypasses average and denominator evaluation")
val direct = bm25_fixed_v1_term_checked(0, 0, 0, 0, 0, 1000).unwrap()
expect(direct.average_length_scaled).to_equal(0)
expect(direct.idf_argument_scaled).to_equal(0)
expect(direct.denominator_scaled).to_equal(0)
expect(direct.weighted).to_equal(0)
val absent = Bm25FieldV1.of(
    "body", ["cat"], [0], [0], 0, 0, 1)
expect(milli_of(bm25_fixed_v1_score_checked([absent]).unwrap())).to_equal(0)
```

</details>

#### derives all five field weights in their closed order

- derives all five field weights in their closed order
- Verify canonical field authority and ordered accumulation
   - Expected: milli_of(score) equals `6344`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("derives all five field weights in their closed order")
step("Verify canonical field authority and ordered accumulation")
val identifier = Bm25FieldV1.of(
    "identifier", ["cat"], [1], [2], 6, 18, 3)
val title = Bm25FieldV1.of(
    "title", ["cat"], [1], [2], 6, 18, 3)
val heading = Bm25FieldV1.of(
    "heading", ["cat"], [1], [2], 6, 18, 3)
val classification = Bm25FieldV1.of(
    "classification", ["cat"], [1], [2], 6, 18, 3)
val body = Bm25FieldV1.of(
    "body", ["cat"], [1], [2], 6, 18, 3)
val score = bm25_fixed_v1_score_checked([
    identifier, title, heading, classification, body,
]).unwrap()
# 469998 * (4 + 4 + 2.5 + 2 + 1) = 6344973 internal -> 6344.
expect(milli_of(score)).to_equal(6344)
```

</details>

#### enforces exact query-term count and UTF-8 byte bounds

- enforces exact query-term count and UTF-8 byte bounds
- Verify 128/129 and 4096/4097 scorer boundaries
   - Expected: bm25_fixed_v1_score_checked([max_bytes]).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("enforces exact query-term count and UTF-8 byte bounds")
step("Verify 128/129 and 4096/4097 scorer boundaries")
val terms_128 = prefix_terms(128)
val ones_128 = repeated_i64(1, 128)
val dfs_128 = repeated_i64(2, 128)
val max_terms = Bm25FieldV1.of(
    "body", terms_128, ones_128, dfs_128, 128, 384, 3)
expect(milli_of(bm25_fixed_v1_score_checked([max_terms]).unwrap())).to_equal(
    60159)
val terms_129 = prefix_terms(129)
val zeros_129 = repeated_i64(0, 129)
val too_many = Bm25FieldV1.of(
    "body", terms_129, zeros_129, zeros_129, 0, 0, 1)
expect(bm25_fixed_v1_score_checked([too_many]).unwrap_err()).to_equal(
    "limit_exceeded")
val bytes_4096 = repeated_ascii(4096)
val bytes_4097 = repeated_ascii(4097)
val max_bytes = Bm25FieldV1.of(
    "body", [bytes_4096], [0], [0], 0, 0, 1)
expect(bm25_fixed_v1_score_checked([max_bytes]).is_ok()).to_equal(true)
val too_many_bytes = Bm25FieldV1.of(
    "body", [bytes_4097], [0], [0], 0, 0, 1)
expect(bm25_fixed_v1_score_checked([too_many_bytes]).unwrap_err()).to_equal(
    "limit_exceeded")
```

</details>

#### accepts tf equal to document length and rejects one greater

- accepts tf equal to document length and rejects one greater
- Verify term-frequency field-length boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts tf equal to document length and rejects one greater")
step("Verify term-frequency field-length boundary")
expect(bm25_fixed_v1_term_checked(
    1, 1, 1, 1, 1, 1000).is_ok()).to_equal(true)
expect(bm25_fixed_v1_term_checked(
    2, 1, 1, 1, 1, 1000).unwrap_err()).to_equal("invalid_request")
```

</details>

### bm25-fixed-v1 deterministic failures

#### returns exact corpus, frequency, average, and logarithm codes

- returns exact corpus, frequency, average, and logarithm codes
- Verify domain failures are typed and stable


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns exact corpus, frequency, average, and logarithm codes")
step("Verify domain failures are typed and stable")
expect(bm25_fixed_v1_term_checked(
    1, 1, 1, 0, 0, 1000).unwrap_err()).to_equal("invalid_corpus_n")
expect(bm25_fixed_v1_term_checked(
    1, 1, 1, 1, 2, 1000).unwrap_err()).to_equal(
        "invalid_document_frequency")
expect(bm25_fixed_v1_term_checked(
    1, 2, 1, 1, 1, 1000).unwrap_err()).to_equal(
        "invalid_average_length")
expect(fixed_ln_checked(0).unwrap_err()).to_equal(
    "invalid_logarithm_input")
expect(bm25_fixed_v1_term_checked(
    0, 0 - 1, 0, 0, 0, 1000).unwrap_err()).to_equal("invalid_request")
expect(bm25_fixed_v1_term_checked(
    0 - 1, 1, 1, 1, 1, 1000).unwrap_err()).to_equal("invalid_request")
expect(bm25_fixed_v1_term_checked(
    1, 1, 0, 1, 1, 1000).unwrap_err()).to_equal(
        "invalid_average_length")
```

</details>

#### rejects array mismatch, noncanonical field order, and unknown weight

- rejects array mismatch, noncanonical field order, and unknown weight
- Verify canonical structural boundaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects array mismatch, noncanonical field order, and unknown weight")
step("Verify canonical structural boundaries")
val mismatch = Bm25FieldV1.of(
    "body", ["cat"], [1, 2], [1], 1, 1, 1)
expect(bm25_fixed_v1_score_checked([mismatch]).unwrap_err()).to_equal(
    "invalid_parallel_arrays")
val title = Bm25FieldV1.of("title", ["cat"], [1], [1], 1, 1, 1)
val identifier = Bm25FieldV1.of(
    "identifier", ["cat"], [1], [1], 1, 1, 1)
expect(bm25_fixed_v1_score_checked([title, identifier]).unwrap_err()).to_equal(
    "invalid_parallel_arrays")
expect(bm25_fixed_v1_term_checked(
    1, 1, 1, 1, 1, 999).unwrap_err()).to_equal(
        "invalid_request")
val empty_term = Bm25FieldV1.of("body", [""], [0], [0], 0, 0, 1)
expect(bm25_fixed_v1_score_checked([empty_term]).unwrap_err()).to_equal(
    "invalid_request")
val unknown_field = Bm25FieldV1.of(
    "summary", ["cat"], [0], [0], 0, 0, 1)
expect(bm25_fixed_v1_score_checked([unknown_field]).unwrap_err()).to_equal(
    "invalid_request")
expect(bm25_score_default_checked(
    [1], [1], 1, 1000000, 0).unwrap_err()).to_equal("invalid_corpus_n")
```

</details>

#### fails closed at multiplication and average-sum boundaries

- fails closed at multiplication and average-sum boundaries
- Verify conceptual i128 values and corpus sums never wrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed at multiplication and average-sum boundaries")
step("Verify conceptual i128 values and corpus sums never wrap")
expect(bm25_fixed_v1_term_checked(
    1, 1, 9223372036854775807, 1, 1, 1000).unwrap_err()).to_equal(
        "score_overflow")
# dl*S*S still fits (5e18), but tf*(K1+S)*S is 1.1e19.
expect(bm25_score_default_checked(
    [5000000], [1], 5000000, 5000000000000, 1).unwrap_err()).to_equal(
        "score_overflow")
expect(avg_doc_len_fixed_checked(
    [9223372036854775807, 1]).unwrap_err()).to_equal("score_overflow")
# IDF's exact first operation is 2*N and must not wrap.
expect(bm25_score_default_checked(
    [1], [1], 1, 1000000,
    9223372036854775807).unwrap_err()).to_equal("score_overflow")
# b*ratio fits, but K1*norm does not; no reassociation is permitted.
expect(bm25_score_default_checked(
    [1], [1], 12, 1, 1).unwrap_err()).to_equal("score_overflow")
```

</details>

#### keeps legacy checked signatures as a hardcoded compatibility vector

- keeps legacy checked signatures as a hardcoded compatibility vector
- Verify compatibility retains its independently computed result
   - Expected: milli_of(legacy) equals `469`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps legacy checked signatures as a hardcoded compatibility vector")
step("Verify compatibility retains its independently computed result")
val legacy = bm25_score_default_checked([1], [2], 6, 6000000, 3).unwrap()
expect(milli_of(legacy)).to_equal(469)
expect(bm25_score_default_checked(
    [1], [1, 2], 2, 2000000, 2).unwrap_err()).to_equal(
        "invalid_parallel_arrays")
```

</details>

### bm25-fixed-v1 public-ID tie rule

#### orders score descending then unsigned UTF-8 document ID ascending

- orders score descending then unsigned UTF-8 document ID ascending
- Verify deterministic score and bytewise ID precedence
   - Expected: bm25_fixed_v1_precedes(tied, "z", tied, "é") is true
   - Expected: bm25_fixed_v1_precedes(tied, "é", tied, "z") is false
   - Expected: bm25_fixed_v1_precedes(tied, "a", tied, "aa") is true
   - Expected: bm25_fixed_v1_precedes(tied, "aa", tied, "a") is false
   - Expected: bm25_fixed_v1_precedes(tied, "a", tied, "a") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("orders score descending then unsigned UTF-8 document ID ascending")
step("Verify deterministic score and bytewise ID precedence")
val tied = Score.from_milli(700)
expect(bm25_fixed_v1_precedes(tied, "z", tied, "é")).to_equal(true)
expect(bm25_fixed_v1_precedes(tied, "é", tied, "z")).to_equal(false)
expect(bm25_fixed_v1_precedes(tied, "a", tied, "aa")).to_equal(true)
expect(bm25_fixed_v1_precedes(tied, "aa", tied, "a")).to_equal(false)
expect(bm25_fixed_v1_precedes(tied, "a", tied, "a")).to_equal(false)
expect(bm25_fixed_v1_precedes(
    Score.from_milli(701), "zz", tied, "aa")).to_equal(true)
```

</details>

### avg_doc_len_fixed

#### computes a fixed-point mean (6.0 -> 6_000_000)

- computes a fixed-point mean (6.0 -> 6_000_000)
- Verify: computes a fixed-point mean (6.0 -> 6_000_000)
   - Expected: avg_doc_len_fixed([4, 6, 8]) equals `6000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("computes a fixed-point mean (6.0 -> 6_000_000)")
step("Verify: computes a fixed-point mean (6.0 -> 6_000_000)")
# @req: REQ-LIB-COMMON-001
expect(avg_doc_len_fixed([4, 6, 8])).to_equal(6000000)  # oracle: 6000000 — named expected value from the requirement
```

</details>

#### keeps fractional averages in fixed-point (5/2 = 2.5 -> 2_500_000)

- keeps fractional averages in fixed-point (5/2 = 2.5 -> 2_500_000)
- Verify: keeps fractional averages in fixed-point (5/2 = 2.5 -> 2_500_000)
   - Expected: avg_doc_len_fixed([2, 3]) equals `2500000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps fractional averages in fixed-point (5/2 = 2.5 -> 2_500_000)")
step("Verify: keeps fractional averages in fixed-point (5/2 = 2.5 -> 2_500_000)")
expect(avg_doc_len_fixed([2, 3])).to_equal(2500000)  # oracle: 2500000 — named expected value from the requirement
```

</details>

#### is 0 for an empty corpus

- is 0 for an empty corpus
- Verify: is 0 for an empty corpus
   - Expected: avg_doc_len_fixed([]) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is 0 for an empty corpus")
step("Verify: is 0 for an empty corpus")
expect(avg_doc_len_fixed([])).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### BM25 absolute-oracle scores (k1=1.2, b=0.75)

#### doc0 (cat x3, dog absent, dl=4) scores 795 milli

- doc0 (cat x3, dog absent, dl=4) scores 795 milli
- Verify: doc0 (cat x3, dog absent, dl=4) scores 795 milli
   - Expected: milli_of(s) equals `795`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("doc0 (cat x3, dog absent, dl=4) scores 795 milli")
step("Verify: doc0 (cat x3, dog absent, dl=4) scores 795 milli")
# tfs aligned to query [cat, dog]; df aligned the same way.
val s = bm25_score_default([3, 0], [2, 2], 4, corpus_avgdl(), 3)
expect(milli_of(s)).to_equal(795)  # oracle: 795 — named expected value from the requirement
```

</details>

#### doc1 (cat x1, dog x2, dl=6) scores 1116 milli

- doc1 (cat x1, dog x2, dl=6) scores 1116 milli
- Verify: doc1 (cat x1, dog x2, dl=6) scores 1116 milli
   - Expected: milli_of(s) equals `1116`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("doc1 (cat x1, dog x2, dl=6) scores 1116 milli")
step("Verify: doc1 (cat x1, dog x2, dl=6) scores 1116 milli")
val s = bm25_score_default([1, 2], [2, 2], 6, corpus_avgdl(), 3)
expect(milli_of(s)).to_equal(1116)  # oracle: 1116 — named expected value from the requirement
```

</details>

#### doc2 (cat absent, dog x2, dl=8) scores 590 milli

- doc2 (cat absent, dog x2, dl=8) scores 590 milli
- Verify: doc2 (cat absent, dog x2, dl=8) scores 590 milli
   - Expected: milli_of(s) equals `590`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("doc2 (cat absent, dog x2, dl=8) scores 590 milli")
step("Verify: doc2 (cat absent, dog x2, dl=8) scores 590 milli")
val s = bm25_score_default([0, 2], [2, 2], 8, corpus_avgdl(), 3)
expect(milli_of(s)).to_equal(590)  # oracle: 590 — named expected value from the requirement
```

</details>

#### a term absent in a doc contributes nothing (tf=0 term dropped)

- a term absent in a doc contributes nothing (tf=0 term dropped)
- Verify: a term absent in a doc contributes nothing (tf=0 term dropped)
   - Expected: milli_of(both) equals `milli_of(cat_only)`
   - Expected: milli_of(cat_only) equals `795`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a term absent in a doc contributes nothing (tf=0 term dropped)")
step("Verify: a term absent in a doc contributes nothing (tf=0 term dropped)")
# doc with only cat present must equal the same doc scored cat-only.
val both = bm25_score_default([3, 0], [2, 2], 4, corpus_avgdl(), 3)
val cat_only = bm25_score_default([3], [2], 4, corpus_avgdl(), 3)
expect(milli_of(both)).to_equal(milli_of(cat_only))
expect(milli_of(cat_only)).to_equal(795)  # oracle: 795 — named expected value from the requirement
```

</details>

### TF-IDF absolute-oracle scores

#### tf=1, df=3, N=3 -> 133 milli (ln(8/7))

- tf=1, df=3, N=3 -> 133 milli (ln(8/7))
- Verify: tf=1, df=3, N=3 -> 133 milli (ln(8/7))
   - Expected: milli_of(s) equals `133`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tf=1, df=3, N=3 -> 133 milli (ln(8/7))")
step("Verify: tf=1, df=3, N=3 -> 133 milli (ln(8/7))")
val s = tfidf_score([1], [3], 3)
expect(milli_of(s)).to_equal(133)  # oracle: 133 — named expected value from the requirement
```

</details>

#### tf=3, df=3, N=3 -> 400 milli (3 * ln(8/7))

- tf=3, df=3, N=3 -> 400 milli (3 * ln(8/7))
- Verify: tf=3, df=3, N=3 -> 400 milli (3 * ln(8/7))
   - Expected: milli_of(s) equals `400`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tf=3, df=3, N=3 -> 400 milli (3 * ln(8/7))")
step("Verify: tf=3, df=3, N=3 -> 400 milli (3 * ln(8/7))")
val s = tfidf_score([3], [3], 3)
expect(milli_of(s)).to_equal(400)  # oracle: 400 — named expected value from the requirement
```

</details>

#### tf=0 contributes 0

- tf=0 contributes 0
- Verify: tf=0 contributes 0
   - Expected: milli_of(s) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tf=0 contributes 0")
step("Verify: tf=0 contributes 0")
val s = tfidf_score([0], [3], 3)
expect(milli_of(s)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### ranking order over the hand corpus

#### ranks doc1 > doc0 > doc2 by BM25 score

- ranks doc1 > doc0 > doc2 by BM25 score
- Verify: ranks doc1 > doc0 > doc2 by BM25 score
   - Expected: ranked.len() equals `3`
   - Expected: ranked[0].doc_id() equals `1`
   - Expected: ranked[1].doc_id() equals `0`
   - Expected: ranked[2].doc_id() equals `2`
   - Expected: milli_of(ranked[0].relevance()) equals `1116`
   - Expected: milli_of(ranked[1].relevance()) equals `795`
   - Expected: milli_of(ranked[2].relevance()) equals `590`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ranks doc1 > doc0 > doc2 by BM25 score")
step("Verify: ranks doc1 > doc0 > doc2 by BM25 score")
val avg = corpus_avgdl()
val d0 = ScoredDoc.of(0, bm25_score_default([3, 0], [2, 2], 4, avg, 3))
val d1 = ScoredDoc.of(1, bm25_score_default([1, 2], [2, 2], 6, avg, 3))
val d2 = ScoredDoc.of(2, bm25_score_default([0, 2], [2, 2], 8, avg, 3))
val ranked = rank_all([d0, d1, d2])
expect(ranked.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(ranked[0].doc_id()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(ranked[1].doc_id()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(ranked[2].doc_id()).to_equal(2)  # oracle: 2 — named expected value from the requirement
# exact scaled scores survive into the ranked output
expect(milli_of(ranked[0].relevance())).to_equal(1116)  # oracle: 1116 — named expected value from the requirement
expect(milli_of(ranked[1].relevance())).to_equal(795)  # oracle: 795 — named expected value from the requirement
expect(milli_of(ranked[2].relevance())).to_equal(590)  # oracle: 590 — named expected value from the requirement
```

</details>

### top_k selection over Score

#### returns the k best in ranked order

- returns the k best in ranked order
- Verify: returns the k best in ranked order
   - Expected: r.len() equals `2`
   - Expected: r[0].doc_id() equals `11`
   - Expected: r[1].doc_id() equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns the k best in ranked order")
step("Verify: returns the k best in ranked order")
val a = ScoredDoc.of(10, Score.from_milli(500))
val b = ScoredDoc.of(11, Score.from_milli(900))
val c = ScoredDoc.of(12, Score.from_milli(700))
val d = ScoredDoc.of(13, Score.from_milli(300))
val r = top_k([a, b, c, d], 2)
expect(r.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(r[0].doc_id()).to_equal(11)  # oracle: 11 — named expected value from the requirement
expect(r[1].doc_id()).to_equal(12)  # oracle: 12 — named expected value from the requirement
```

</details>

#### breaks ties by ascending id (deterministic, no stability reliance)

- breaks ties by ascending id (deterministic, no stability reliance)
- Verify: breaks ties by ascending id (deterministic, no stability reliance)
   - Expected: r.len() equals `3`
   - Expected: r[0].doc_id() equals `2`
   - Expected: r[1].doc_id() equals `5`
   - Expected: r[2].doc_id() equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("breaks ties by ascending id (deterministic, no stability reliance)")
step("Verify: breaks ties by ascending id (deterministic, no stability reliance)")
# three docs share score 700; ids 5, 2, 9 must come out 2, 5, 9.
val x = ScoredDoc.of(5, Score.from_milli(700))
val y = ScoredDoc.of(2, Score.from_milli(700))
val z = ScoredDoc.of(9, Score.from_milli(700))
val r = top_k([x, y, z], 3)
expect(r.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(r[0].doc_id()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(r[1].doc_id()).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(r[2].doc_id()).to_equal(9)  # oracle: 9 — named expected value from the requirement
```

</details>

#### mixed tie and ordering: top score wins, then id tie-break

- mixed tie and ordering: top score wins, then id tie-break
- Verify: mixed tie and ordering: top score wins, then id tie-break
   - Expected: r[0].doc_id() equals `3`
   - Expected: r[1].doc_id() equals `8`
   - Expected: r[2].doc_id() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("mixed tie and ordering: top score wins, then id tie-break")
step("Verify: mixed tie and ordering: top score wins, then id tie-break")
val p = ScoredDoc.of(8, Score.from_milli(900))
val q = ScoredDoc.of(3, Score.from_milli(900))
val rr = ScoredDoc.of(1, Score.from_milli(400))
val r = top_k([p, q, rr], 3)
expect(r[0].doc_id()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(r[1].doc_id()).to_equal(8)  # oracle: 8 — named expected value from the requirement
expect(r[2].doc_id()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### k larger than corpus returns all, k=0 returns none

- k larger than corpus returns all, k=0 returns none
- Verify: k larger than corpus returns all, k=0 returns none
   - Expected: top_k([a, b], 9).len() equals `2`
   - Expected: top_k([a, b], 0).len() equals `0`
   - Expected: top_k([], 3).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("k larger than corpus returns all, k=0 returns none")
step("Verify: k larger than corpus returns all, k=0 returns none")
val a = ScoredDoc.of(1, Score.from_milli(100))
val b = ScoredDoc.of(2, Score.from_milli(200))
expect(top_k([a, b], 9).len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(top_k([a, b], 0).len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(top_k([], 3).len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f97b07b37eca4729ec744a938bbb5a2e464f9025bbbaab6305799924d319f433`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f97b07b37eca4729ec744a938bbb5a2e464f9025bbbaab6305799924d319f433`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f97b07b37eca4729ec744a938bbb5a2e464f9025bbbaab6305799924d319f433`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/search/ranking_spec.spl
mirror: doc/06_spec/01_unit/lib/common/search/ranking_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/search/ranking_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/search/ranking_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/search/ranking_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 44 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/search/ranking_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the hand-computed term intermediate vector exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/search/ranking_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches fixed-ln reduction boundary vectors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/search/ranking_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts both document-frequency boundaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
