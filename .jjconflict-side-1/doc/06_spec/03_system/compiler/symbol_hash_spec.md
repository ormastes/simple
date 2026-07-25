# Symbol Hash Specification

> <details>

<!-- sdn-diagram:id=symbol_hash_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=symbol_hash_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

symbol_hash_spec -> std
symbol_hash_spec -> std_lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=symbol_hash_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Symbol Hash Specification

## Scenarios

#### Hash empty symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an empty string"
val symbol = ""
# When "hashing the symbol"
val hash = hash_symbol(symbol)
# Then "it should have symbol type bit set"
expect(is_symbol_hash(hash)).to_equal(true)
```

</details>

#### Same symbol produces same hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "two identical empty symbols"
val s1 = ""
val s2 = ""
# When "hashing both symbols"
val h1 = hash_symbol(s1)
val h2 = hash_symbol(s2)
# Then "they should produce the same hash"
expect(h1).to_equal(h2)
```

</details>

#### Check symbol type bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a hashed empty symbol"
val hash = hash_symbol("")
# When "checking the type bit"
val has_type_bit = is_symbol_hash(hash)
# Then "it should return true"
expect(has_type_bit).to_equal(true)
```

</details>

#### Check non-symbol hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a regular integer without type tag"
val hash: i64 = 12345
# When "checking if it's a symbol hash"
val is_symbol = is_symbol_hash(hash)
# Then "it should return false"
expect(is_symbol).to_equal(false)
```

</details>

#### Untag symbol hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a tagged empty symbol hash"
val symbol = ""
val tagged = hash_symbol(symbol)
# When "removing the tag"
val untagged = untag_symbol_hash(tagged)
# Then "the type bit should be removed"
expect(is_symbol_hash(untagged)).to_equal(false)
# And "it should equal the raw hash"
val raw = get_raw_hash(symbol)
expect(untagged).to_equal(raw)
```

</details>

#### Get raw hash matches untagged hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an empty symbol"
val symbol = ""
# When "computing raw hash and untagging hashed symbol"
val raw = get_raw_hash(symbol)
val untagged = untag_symbol_hash(hash_symbol(symbol))
# Then "they should be equal"
expect(raw).to_equal(untagged)
```

</details>

#### Hash multiple symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an array of empty symbols"
val symbols = ["", "", ""]
# When "hashing all symbols"
val hashes = hash_symbols(symbols)
# Then "it should return array of same length"
expect(hashes.length()).to_equal(3)
# And "all hashes should be tagged"
for h in hashes:
    expect(is_symbol_hash(h)).to_equal(true)
```

</details>

#### Detect no collision for same symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "the same empty symbol twice"
val s1 = ""
val s2 = ""
# When "checking for collision"
val collision = has_collision(s1, s2)
# Then "it should return false (same string, not a collision)"
expect(collision).to_equal(false)
```

</details>

#### Polynomial hash is deterministic

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an empty symbol"
val symbol = ""
# When "computing poly hash multiple times"
val h1 = poly_hash(symbol)
val h2 = poly_hash(symbol)
val h3 = poly_hash(symbol)
# Then "all should be equal"
expect(h1).to_equal(h2)
expect(h2).to_equal(h3)
```

</details>

#### Empty string has zero raw hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an empty string"
val symbol = ""
# When "computing raw hash"
val hash = poly_hash(symbol)
# Then "it should be zero"
expect(hash).to_equal(0)
```

</details>

#### Check all symbols unique

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an array with duplicate empty symbols"
val symbols = ["", ""]
# When "hashing all symbols"
val hashes = hash_symbols(symbols)
# Then "the hashes should be equal"
expect(hashes[0]).to_equal(hashes[1])
```

</details>

#### Detect duplicate hashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an array with duplicate empty symbols"
val symbols = ["", ""]
# When "hashing all symbols"
val hashes = hash_symbols(symbols)
# Then "the hashes should be equal"
expect(hashes[0]).to_equal(hashes[1])
```

</details>

#### Tagging and untagging round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a raw hash value"
val symbol = ""
val raw = get_raw_hash(symbol)
# When "tagging then untagging"
val tagged = raw | SYMBOL_TYPE_BIT
val untagged = untag_symbol_hash(tagged)
# Then "it should return the original value"
expect(untagged).to_equal(raw)
```

</details>

#### Symbol type bit position

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "the symbol type bit constant"
val bit = SYMBOL_TYPE_BIT
# When "checking the bit value"
# Then "it should equal 2^62"
expect(bit).to_equal(4611686018427387904)
```

</details>

#### Hash base is 31

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "the hash base constant"
val base = HASH_BASE
# When "checking the value"
# Then "it should equal 31"
expect(base).to_equal(31)
```

</details>

#### Collision probability increases with more symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "different numbers of symbols"
val p10 = collision_probability(10)
val p100 = collision_probability(100)
val p1000 = collision_probability(1000)
# When "comparing probabilities"
# Then "probability should increase with more symbols"
expect(p100 > p10).to_equal(true)
expect(p1000 > p100).to_equal(true)
```

</details>

#### Collision probability is very small for few symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a small number of symbols"
val n = 100
# When "computing collision probability"
val prob = collision_probability(n)
# Then "it should be extremely small (< 0.0001)"
expect(prob < 0.0001).to_equal(true)
```

</details>

#### Hash distribution for common symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an empty symbol list"
val symbols = []
# When "computing hash distribution"
val dist = hash_distribution(symbols)
# Then "there should be no buckets"
expect(dist.len()).to_equal(0)
```

</details>

#### Hash wrapping arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an empty symbol"
val symbol = ""
# When "hashing the symbol"
val hash = hash_symbol(symbol)
# Then "it should not panic and produce a valid tagged hash"
expect(is_symbol_hash(hash)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/symbol_hash_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
