# Cache Correctness Specification

> <details>

<!-- sdn-diagram:id=cache_correctness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cache_correctness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cache_correctness_spec -> std
cache_correctness_spec -> verification
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cache_correctness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cache Correctness Specification

## Scenarios

### Verification Cache

#### returns nil for unknown entries

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = VerificationCache.new("/tmp/test-vcache-empty")
val fp = Fingerprint.from_hashes("h1", "h2", [], "v4.x")
val result = cache.lookup("unknown.spl", fp)
expect(result).to_be_nil()
```

</details>

#### stores and retrieves an entry with matching fingerprint

1. var cache = VerificationCache new

2. cache store
   - Expected: entry.fingerprint equals `fp.combined`
   - Expected: entry.state equals `VerificationState.Verified`
   - Expected: "nil cache entry" equals `stored cache entry`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = VerificationCache.new("/tmp/test-vcache-store")
val fp = Fingerprint.from_hashes("src1", "lean1", [], "v4.x")
cache.store("my_module.spl", fp, VerificationState.Verified, {}, "v4.x")
val result = cache.lookup("my_module.spl", fp)
expect(result.?).to_be(true)
match result:
    case Some(entry):
        expect(entry.fingerprint).to_equal(fp.combined)
        expect(entry.state).to_equal(VerificationState.Verified)
    case nil:
        expect("nil cache entry").to_equal("stored cache entry")
```

</details>

#### returns nil when fingerprint has changed (stale detection)

1. var cache = VerificationCache new

2. cache store


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = VerificationCache.new("/tmp/test-vcache-stale")
val fp_old = Fingerprint.from_hashes("src1", "lean1", [], "v4.x")
cache.store("stale_module.spl", fp_old, VerificationState.Verified, {}, "v4.x")
# Now compute a different fingerprint (source changed)
val fp_new = Fingerprint.from_hashes("src2_changed", "lean1", [], "v4.x")
val result = cache.lookup("stale_module.spl", fp_new)
expect(result).to_be_nil()
```

</details>

#### never returns a Verified result when fingerprint mismatches

1. var cache = VerificationCache new

2. cache store
   - Expected: fp_original.source_hash equals `original`
   - Expected: fp_changed.source_hash equals `modified`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = VerificationCache.new("/tmp/test-vcache-safety")
val fp_original = Fingerprint.from_hashes("original", "lean_ok", [], "v4.x")
cache.store("safety.spl", fp_original, VerificationState.Verified, {}, "v4.x")
# Simulate a semantic change by altering the source hash
val fp_changed = Fingerprint.from_hashes("modified", "lean_ok", [], "v4.x")
expect(fp_original.source_hash).to_equal("original")
expect(fp_changed.source_hash).to_equal("modified")
expect(fp_original.combined).to_not_equal(fp_changed.combined)
val result = cache.lookup("safety.spl", fp_changed)
# The safety invariant: stale entries must not be returned
expect(result).to_be_nil()
```

</details>

#### tracks cache statistics for hits and misses

1. var cache = VerificationCache new

2. cache store

3. cache lookup

4. cache lookup

5. cache lookup
   - Expected: s.hits equals `1`
   - Expected: s.misses equals `1`
   - Expected: s.stale equals `1`
   - Expected: s.total_entries equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = VerificationCache.new("/tmp/test-vcache-stats")
val fp = Fingerprint.from_hashes("s1", "l1", [], "v4.x")
cache.store("hit.spl", fp, VerificationState.Verified, {}, "v4.x")

# Hit
cache.lookup("hit.spl", fp)
# Miss
cache.lookup("nonexistent.spl", fp)
# Stale
val fp2 = Fingerprint.from_hashes("s2", "l1", [], "v4.x")
cache.lookup("hit.spl", fp2)

val s = cache.stats()
expect(s.hits).to_equal(1)
expect(s.misses).to_equal(1)
expect(s.stale).to_equal(1)
expect(s.total_entries).to_equal(1)
```

</details>

#### formats cache stats as human-readable text

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = CacheStats(total_entries: 5, hits: 3, misses: 1, stale: 1)
val formatted = s.format()
expect(formatted).to_contain("5 entries")
expect(formatted).to_contain("3 hits")
expect(formatted).to_contain("1 misses")
expect(formatted).to_contain("1 stale")
```

</details>

#### invalidate_dependents

#### removes cached entries for units depending on changed module

1. var cache = VerificationCache new

2. cache store

3. cache store

4. var unit a = ProofUnit create

5. var unit b = ProofUnit create

6. unit b = unit b with dependencies

7. cache invalidate dependents
   - Expected: entry.fingerprint equals `fp_a.combined`
   - Expected: "nil cache entry" equals `preserved cache entry`


<details>
<summary>Executable SPipe</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = VerificationCache.new("/tmp/test-vcache-invalidate")
val fp_a = Fingerprint.from_hashes("a", "la", [], "v4.x")
val fp_b = Fingerprint.from_hashes("b", "lb", [], "v4.x")
cache.store("a.spl", fp_a, VerificationState.Verified, {}, "v4.x")
cache.store("b.spl", fp_b, VerificationState.Verified, {}, "v4.x")

# Unit b depends on module "base_defs"
var unit_a = ProofUnit.create("a.spl", "*", "Verification.A", "a.lean")
var unit_b = ProofUnit.create("b.spl", "*", "Verification.B", "b.lean")
unit_b = unit_b.with_dependencies(["base_defs"])

cache.invalidate_dependents("base_defs", [unit_a, unit_b])

# a.spl should still be cached (no dependency on base_defs)
val result_a = cache.lookup("a.spl", fp_a)
match result_a:
    case Some(entry):
        expect(entry.fingerprint).to_equal(fp_a.combined)
    case nil:
        expect("nil cache entry").to_equal("preserved cache entry")

# b.spl should have been invalidated
val result_b = cache.lookup("b.spl", fp_b)
expect(result_b).to_be_nil()
```

</details>

#### removes transitive dependents of a changed module

1. var cache = VerificationCache new

2. cache store

3. cache store

4. var unit b = ProofUnit create

5. var unit c = ProofUnit create

6. unit b = unit b with dependencies

7. unit c = unit c with dependencies

8. cache invalidate dependents


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = VerificationCache.new("/tmp/test-vcache-invalidate-transitive")
val fp_b = Fingerprint.from_hashes("b", "lb", [], "v4.x")
val fp_c = Fingerprint.from_hashes("c", "lc", [], "v4.x")
cache.store("b.spl", fp_b, VerificationState.Verified, {}, "v4.x")
cache.store("c.spl", fp_c, VerificationState.Verified, {}, "v4.x")

var unit_b = ProofUnit.create("b.spl", "*", "Verification.B", "b.lean")
var unit_c = ProofUnit.create("c.spl", "*", "Verification.C", "c.lean")
unit_b = unit_b.with_dependencies(["Verification.A"])
unit_c = unit_c.with_dependencies(["Verification.B"])

cache.invalidate_dependents("Verification.A", [unit_b, unit_c])

expect(cache.lookup("b.spl", fp_b)).to_be_nil()
expect(cache.lookup("c.spl", fp_c)).to_be_nil()
```

</details>

#### removes all cached members of a dependent cycle

1. var cache = VerificationCache new

2. cache store

3. cache store

4. var unit a = ProofUnit create

5. var unit b = ProofUnit create

6. unit a = unit a with dependencies

7. unit b = unit b with dependencies

8. cache invalidate dependents


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = VerificationCache.new("/tmp/test-vcache-invalidate-cycle")
val fp_a = Fingerprint.from_hashes("a", "la", [], "v4.x")
val fp_b = Fingerprint.from_hashes("b", "lb", [], "v4.x")
cache.store("a.spl", fp_a, VerificationState.Verified, {}, "v4.x")
cache.store("b.spl", fp_b, VerificationState.Verified, {}, "v4.x")

var unit_a = ProofUnit.create("a.spl", "*", "Verification.A", "a.lean")
var unit_b = ProofUnit.create("b.spl", "*", "Verification.B", "b.lean")
unit_a = unit_a.with_dependencies(["Verification.B"])
unit_b = unit_b.with_dependencies(["Verification.A"])

cache.invalidate_dependents("Verification.A", [unit_a, unit_b])

expect(cache.lookup("a.spl", fp_a)).to_be_nil()
expect(cache.lookup("b.spl", fp_b)).to_be_nil()
```

</details>

#### removes field-wrapper semantic dependents and wrapped-reference cycles

1. var cache = VerificationCache new

2. cache store

3. cache store

4. var unit a = ProofUnit create

5. var unit b = ProofUnit create

6. unit a = unit a with dependencies

7. unit b = unit b with dependencies

8. cache invalidate dependents


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = VerificationCache.new("/tmp/test-vcache-field-wrapper-cycle")
val fp_a = Fingerprint.from_hashes("a", "la", [], "v4.x")
val fp_b = Fingerprint.from_hashes("b", "lb", [], "v4.x")
cache.store("a.spl", fp_a, VerificationState.Verified, {}, "v4.x")
cache.store("b.spl", fp_b, VerificationState.Verified, {}, "v4.x")

var unit_a = ProofUnit.create("a.spl", "A", "Verification.A", "a.lean")
var unit_b = ProofUnit.create("b.spl", "B", "Verification.B", "b.lean")
unit_a = unit_a.with_dependencies(["B.value.field_wrapper"])
unit_b = unit_b.with_dependencies(["a.spl"])

cache.invalidate_dependents("B.value.field_wrapper", [unit_a, unit_b])

expect(cache.lookup("a.spl", fp_a)).to_be_nil()
expect(cache.lookup("b.spl", fp_b)).to_be_nil()
```

</details>

#### clear

#### empties the cache completely

1. var cache = VerificationCache new

2. cache store

3. cache store
   - Expected: cache.stats().total_entries equals `2`

4. cache clear
   - Expected: cache.stats().total_entries equals `0`
   - Expected: cache.stats().hits equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = VerificationCache.new("/tmp/test-vcache-clear")
val fp = Fingerprint.from_hashes("x", "y", [], "v4.x")
cache.store("one.spl", fp, VerificationState.Verified, {}, "v4.x")
cache.store("two.spl", fp, VerificationState.Failed, {}, "v4.x")
expect(cache.stats().total_entries).to_equal(2)

cache.clear()
expect(cache.stats().total_entries).to_equal(0)
expect(cache.stats().hits).to_equal(0)
```

</details>

#### Fingerprint

#### produces deterministic hashes for identical input

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fp1 = Fingerprint.from_hashes("src", "lean", ["dep1"], "v4.x")
val fp2 = Fingerprint.from_hashes("src", "lean", ["dep1"], "v4.x")
expect(fp1.matches(fp2)).to_be(true)
expect(fp1.combined).to_equal(fp2.combined)
```

</details>

#### produces different hashes for different input

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fp1 = Fingerprint.from_hashes("src_a", "lean", [], "v4.x")
val fp2 = Fingerprint.from_hashes("src_b", "lean", [], "v4.x")
expect(fp1.combined).to_not_equal(fp2.combined)
```

</details>

#### includes toolchain version in fingerprint

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fp1 = Fingerprint.from_hashes("src", "lean", [], "v4.3.0")
val fp2 = Fingerprint.from_hashes("src", "lean", [], "v4.4.0")
expect(fp1.combined).to_not_equal(fp2.combined)
```

</details>

#### includes dependency hashes in fingerprint

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fp1 = Fingerprint.from_hashes("src", "lean", ["dep_v1"], "v4.x")
val fp2 = Fingerprint.from_hashes("src", "lean", ["dep_v2"], "v4.x")
expect(fp1.combined).to_not_equal(fp2.combined)
```

</details>

#### includes public ABI accessor and field-wrapper semantic hashes

<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val abi_v1 = public_abi_fingerprint("B", "field:value:WrappedA", ["get_value", "set_value"])
val get_v1 = accessor_fingerprint("B", "get_value", "fn() -> WrappedA", "body:v1")
val set_v1 = accessor_fingerprint("B", "set_value", "fn(WrappedA) -> void", "body:v1")
val wrapper_v1 = field_wrapper_fingerprint("B", "value", "WrappedA", [get_v1, set_v1])
val dep_v1 = dependency_semantic_fingerprint("B", abi_v1, get_v1 + "|" + set_v1, wrapper_v1)

val abi_v2 = public_abi_fingerprint("B", "field:value:WrappedA", ["get_value", "set_value"])
val get_v2 = accessor_fingerprint("B", "get_value", "fn() -> WrappedA", "body:v2")
val set_v2 = accessor_fingerprint("B", "set_value", "fn(WrappedA) -> void", "body:v1")
val wrapper_v2 = field_wrapper_fingerprint("B", "value", "WrappedA", [get_v2, set_v2])
val dep_v2 = dependency_semantic_fingerprint("B", abi_v2, get_v2 + "|" + set_v2, wrapper_v2)

val fp1 = Fingerprint.from_hashes_with_semantics("src", "lean", [], [dep_v1], "v4.x")
val fp2 = Fingerprint.from_hashes_with_semantics("src", "lean", [], [dep_v2], "v4.x")
expect(fp1.combined).to_not_equal(fp2.combined)
```

</details>

#### fails closed when only public ABI accessor semantics change

1. var cache = VerificationCache new

2. cache store


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = VerificationCache.new("/tmp/test-vcache-semantic-field-wrapper")
val abi_v1 = public_abi_fingerprint("B", "field:value:WrappedA", ["get_value", "set_value"])
val get_v1 = accessor_fingerprint("B", "get_value", "fn() -> WrappedA", "body:v1")
val set_v1 = accessor_fingerprint("B", "set_value", "fn(WrappedA) -> void", "body:v1")
val wrapper_v1 = field_wrapper_fingerprint("B", "value", "WrappedA", [get_v1, set_v1])
val dep_v1 = dependency_semantic_fingerprint("B", abi_v1, get_v1 + "|" + set_v1, wrapper_v1)

val abi_v2 = public_abi_fingerprint("B", "field:value:WrappedA", ["get_value", "set_value"])
val get_v2 = accessor_fingerprint("B", "get_value", "fn() -> WrappedA", "body:v2")
val set_v2 = accessor_fingerprint("B", "set_value", "fn(WrappedA) -> void", "body:v1")
val wrapper_v2 = field_wrapper_fingerprint("B", "value", "WrappedA", [get_v2, set_v2])
val dep_v2 = dependency_semantic_fingerprint("B", abi_v2, get_v2 + "|" + set_v2, wrapper_v2)

val fp_v1 = Fingerprint.from_hashes_with_semantics("same-src", "same-lean", [], [dep_v1], "v4.x")
val fp_v2 = Fingerprint.from_hashes_with_semantics("same-src", "same-lean", [], [dep_v2], "v4.x")
cache.store("a_depends_on_b.spl", fp_v1, VerificationState.Verified, {}, "v4.x")
expect(cache.lookup("a_depends_on_b.spl", fp_v2)).to_be_nil()
```

</details>

#### round-trips through to_text and from_text

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sem = accessor_fingerprint("B", "get_value", "fn() -> WrappedA", "body:v1")
val fp = Fingerprint.from_hashes_with_semantics("abc", "def", ["g1", "g2"], [sem], "v4.x")
val serialized = fp.to_text()
val restored = Fingerprint.from_text(serialized)
match restored:
    case Some(fp2):
        expect(fp.matches(fp2)).to_be(true)
        expect(fp2.source_hash).to_equal("abc")
        expect(fp2.lean_hash).to_equal("def")
        expect(fp2.semantic_hashes).to_equal([sem])
        expect(fp2.toolchain_version).to_equal("v4.x")
    case nil:
        expect("nil fingerprint").to_equal("restored fingerprint")
```

</details>

#### returns nil for malformed text

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Fingerprint.from_text("incomplete")
expect(result).to_be_nil()
```

</details>

#### simple_hash

#### returns consistent results for same input

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = simple_hash("hello world")
val h2 = simple_hash("hello world")
expect(h1).to_equal(h2)
```

</details>

#### returns different results for different input

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = simple_hash("hello")
val h2 = simple_hash("world")
expect(h1).to_not_equal(h2)
```

</details>

#### handles empty string

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = simple_hash("")
expect(h.len() > 0).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/00_formal_verification/compiler/cache_correctness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Verification Cache

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
