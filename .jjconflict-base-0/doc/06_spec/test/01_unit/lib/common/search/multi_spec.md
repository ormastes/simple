# Multi Specification

> <details>

<!-- sdn-diagram:id=multi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multi_spec -> std
multi_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multi Specification

## Scenarios

### AhoCorasick canonical fixture {he,she,his,hers} over ushers

#### finds she[1,4), he[2,4), hers[2,6) and not his — exact positions

- expected push
- expected push
- expected push
   - Expected: canon(ac_keys(ms)) equals `canon(expected)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ushers = u(0) s(1) h(2) e(3) r(4) s(5)
# she : s1 h2 e3 -> [1,4)   he : h2 e3 -> [2,4)
# hers: h2 e3 r4 s5 -> [2,6)   his: absent
# ids: he=0, she=1, his=2, hers=3
val pats = ["he", "she", "his", "hers"]
val plist = build_patterns(pats)
val h = Haystack.new("ushers".bytes())
val ms = find_multi(h, plist)
expect(ms.len()).to_equal(3)
var expected: [i64] = []
expected.push(triple_key(1, 1, 4))
expected.push(triple_key(0, 2, 4))
expected.push(triple_key(3, 2, 6))
expect(canon(ac_keys(ms))).to_equal(canon(expected))
```

</details>

#### agrees with the independent naive per-pattern oracle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pats = ["he", "she", "his", "hers"]
expect(run_ac("ushers", pats)).to_equal(run_oracle("ushers", pats))
```

</details>

### AhoCorasick suffix-overlap fixture

#### emits both a pattern and its suffix pattern at the same end

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# {hers, ers, rs} over hers -> hers[0,4), ers[1,4), rs[2,4)
val pats = ["hers", "ers", "rs"]
val plist = build_patterns(pats)
val h = Haystack.new("hers".bytes())
val ms = find_multi(h, plist)
expect(ms.len()).to_equal(3)
expect(run_ac("hers", pats)).to_equal(run_oracle("hers", pats))
```

</details>

#### one pattern is a strict suffix of another (oracle parity)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# {abc, bc, c} over xabcabc
val pats = ["abc", "bc", "c"]
expect(run_ac("xabcabc", pats)).to_equal(run_oracle("xabcabc", pats))
```

</details>

### AhoCorasick overlapping + repeated patterns

#### repeated needle, multiple non-overlapping & overlapping hits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# {aa, a} over aaaa : a at 0,1,2,3 ; aa at 0,1,2
val pats = ["aa", "a"]
expect(run_ac("aaaa", pats)).to_equal(run_oracle("aaaa", pats))
```

</details>

#### overlapping distinct patterns share characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# {abab, bab, ab} over ababab
val pats = ["abab", "bab", "ab"]
expect(run_ac("ababab", pats)).to_equal(run_oracle("ababab", pats))
```

</details>

### AhoCorasick edge cases

#### no matches when patterns absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pats = ["xyz", "qqq"]
val res = run_ac("abcdef", pats)
expect(res).to_equal(run_oracle("abcdef", pats))
# naive oracle finds nothing -> canonical empty encoding
expect(res).to_equal("")
```

</details>

#### pattern equal to whole haystack

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plist = build_patterns(["hello"])
val h = Haystack.new("hello".bytes())
val ms = find_multi(h, plist)
expect(ms.len()).to_equal(1)
expect(ms[0].start()).to_equal(0)
expect(ms[0].end()).to_equal(5)
expect(ms[0].pattern()).to_equal(0)
```

</details>

#### single-char patterns across the text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pats = ["a", "e", "i"]
expect(run_ac("aeiouaei", pats)).to_equal(run_oracle("aeiouaei", pats))
```

</details>

#### empty pattern in set is skipped, others still match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "" should produce no spans; "ab" still matches in "xabyab"
val pats = ["", "ab"]
expect(run_ac("xabyab", pats)).to_equal(run_oracle("xabyab", pats))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/search/multi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AhoCorasick canonical fixture {he,she,his,hers} over ushers
- AhoCorasick suffix-overlap fixture
- AhoCorasick overlapping + repeated patterns
- AhoCorasick edge cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
