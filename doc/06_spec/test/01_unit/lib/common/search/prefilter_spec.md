# Prefilter Specification

> <details>

<!-- sdn-diagram:id=prefilter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=prefilter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

prefilter_spec -> std
prefilter_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=prefilter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Prefilter Specification

## Scenarios

### Prefilter literal screen -> candidate -> verify

#### pure-literal: candidates superset true matches, result equals oracle

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = t_abracadabra()
val patb: [u8] = [0x61u8, 0x62u8, 0x72u8]
val truth = naive_starts(text, patb)
expect(truth.len()).to_equal(2)
expect(truth[0]).to_equal(0)
expect(truth[1]).to_equal(7)

val hay = Haystack.new(text)
val pat = Pattern.new(patb)
val pf = Prefilter.literal(pat)

val cands = pf.candidates(hay)
expect(is_superset(cands, truth)).to_equal(true)

val result = span_starts(pf.run(hay))
expect(lists_equal(result, truth)).to_equal(true)
```

</details>

#### trigram screen on a longer pattern keeps the no-false-negative property

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = t_abracadabra()
val patb: [u8] = [0x63u8, 0x61u8, 0x64u8, 0x61u8, 0x62u8, 0x72u8, 0x61u8]
val truth = naive_starts(text, patb)
expect(truth.len()).to_equal(1)
expect(truth[0]).to_equal(4)

val hay = Haystack.new(text)
val pat = Pattern.new(patb)
val pf = Prefilter.trigram(pat, 2)
expect(pf.gram_len()).to_equal(3)
expect(pf.gram_at(0)).to_equal(0x64u8)

val cands = pf.candidates(hay)
expect(is_superset(cands, truth)).to_equal(true)

val result = span_starts(pf.run(hay))
expect(lists_equal(result, truth)).to_equal(true)
```

</details>

#### selectivity: prefilter rejects most positions

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = t_abracadabra()
val patb: [u8] = [0x61u8, 0x62u8, 0x72u8]
val hay = Haystack.new(text)
val pat = Pattern.new(patb)
val pf = Prefilter.literal(pat)

val cands = pf.candidates(hay)
val scan_positions = text.len() - patb.len() + 1
expect(cands.len()).to_equal(2)
expect(cands.len() < scan_positions).to_equal(true)
val rejected = scan_positions - cands.len()
expect(rejected > 0).to_equal(true)
```

</details>

#### false-positive candidate is removed by verify

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = t_abracadabra()
val patb: [u8] = [0x61u8, 0x62u8, 0x72u8, 0x78u8]
val truth = naive_starts(text, patb)
expect(truth.len()).to_equal(0)

val hay = Haystack.new(text)
val pat = Pattern.new(patb)
val pf = Prefilter.with_gram(pat, 0, 2)

val cands = pf.candidates(hay)
expect(cands.len() > 0).to_equal(true)
expect(is_superset(cands, truth)).to_equal(true)
val result = span_starts(pf.run(hay))
expect(result.len()).to_equal(0)
expect(lists_equal(result, truth)).to_equal(true)
```

</details>

#### no-false-negative under a repeating single-byte text

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text: [u8] = [0x61u8, 0x61u8, 0x61u8, 0x61u8, 0x61u8]
val patb: [u8] = [0x61u8, 0x61u8]
val truth = naive_starts(text, patb)
expect(truth.len()).to_equal(4)

val hay = Haystack.new(text)
val pat = Pattern.new(patb)
val pf = Prefilter.literal(pat)

val cands = pf.candidates(hay)
expect(is_superset(cands, truth)).to_equal(true)
val result = span_starts(pf.run(hay))
expect(lists_equal(result, truth)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/search/prefilter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Prefilter literal screen -> candidate -> verify

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
