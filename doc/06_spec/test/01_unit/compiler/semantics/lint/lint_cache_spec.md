# Lint Cache Specification

> Tests the incremental hash-based lint cache used by the required_comment lint rule. The cache avoids re-running lint on an AST scope whose hash has not changed. It also supports symbol-reference invalidation: if a symbol depended on by a cached result changes, the cached entry is invalidated even if the enclosing scope hash is unchanged.

<!-- sdn-diagram:id=lint_cache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lint_cache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lint_cache_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lint_cache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lint Cache Specification

Tests the incremental hash-based lint cache used by the required_comment lint rule. The cache avoids re-running lint on an AST scope whose hash has not changed. It also supports symbol-reference invalidation: if a symbol depended on by a cached result changes, the cached entry is invalidated even if the enclosing scope hash is unchanged.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #REQC-AC5, #REQC-AC6 |
| Category | Compiler \| Semantics \| Lint \| Cache |
| Difficulty | 3/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/compiler/semantics/lint/lint_cache_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the incremental hash-based lint cache used by the required_comment lint
rule. The cache avoids re-running lint on an AST scope whose hash has not
changed. It also supports symbol-reference invalidation: if a symbol depended
on by a cached result changes, the cached entry is invalidated even if the
enclosing scope hash is unchanged.

## Key Concepts

| Concept | Description |
|---------|-------------|
| scope_hash | FNV-1a hash of the serialized AST of an enclosing function scope |
| cache key | "file_path::scope_name" text key |
| cache hit | scope_hash matches stored hash -> return cached warnings |
| cache miss | scope_hash differs or key absent -> re-run lint, store result |
| symbol_deps | List of symbol names referenced inside a dangerous keyword call |
| symbol_index | Reverse map: symbol_name -> [cache_key] |
| invalidate_symbol | Removes all cache entries that depended on a given symbol |
| invalidate_file | Recomputes per-decl hashes and invalidates changed entries + their deps |

## Scenarios

### lint cache — store and lookup

#### when a result is stored and the hash is unchanged

#### cache lookup returns the stored warnings (cache hit)

1. var cache = make empty cache
2. cache store test
   - Expected: result.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = make_empty_cache()
val key = "src/foo.spl::my_fn"
val h = make_scope_hash("pass_" + "todo body content")
cache_store_test(cache, key, h, ["REQC001"], [])
val result = cache_lookup_test(cache, key, h)
expect(result.?).to_equal(true)
```

</details>

#### cache hit returns the exact stored warning codes

1. var cache = make empty cache
2. cache store test
3. nil: fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = make_empty_cache()
val key = "src/foo.spl::check_fn"
val h = make_scope_hash("pass_do_" + "nothing no comment")
cache_store_test(cache, key, h, ["REQC001"], [])
val result = cache_lookup_test(cache, key, h)
match result:
    Some(ws): expect(ws.len()).to_equal(1)
    nil: fail("cache hit should return stored warning codes")
```

</details>

#### cache hit can return an empty warning list (clean scope)

1. var cache = make empty cache
2. cache store test
3. nil: fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = make_empty_cache()
val key = "src/bar.spl::clean_fn"
val h = make_scope_hash("pass_" + "todo(\"reason\") with comment")
cache_store_test(cache, key, h, [], [])
val result = cache_lookup_test(cache, key, h)
match result:
    Some(ws): expect(ws.len()).to_equal(0)
    nil: fail("cache hit should return empty clean warning list")
```

</details>

#### when the cache is empty

#### lookup returns nil for an unknown key

1. var cache = make empty cache
   - Expected: result.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = make_empty_cache()
val result = cache_lookup_test(cache, "src/unknown.spl::fn", 12345)
expect(result.?).to_equal(false)
```

</details>

### lint cache — cache miss on hash change

#### when the scope hash has changed

#### cache lookup returns nil (cache miss)

1. var cache = make empty cache
2. cache store test
   - Expected: result.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = make_empty_cache()
val key = "src/mod.spl::changed_fn"
val old_hash = make_scope_hash("old body")
val new_hash = make_scope_hash("new body with extra statement")
cache_store_test(cache, key, old_hash, ["REQC001"], [])
val result = cache_lookup_test(cache, key, new_hash)
expect(result.?).to_equal(false)
```

</details>

#### after a miss the caller re-runs lint and can store a fresh result

1. var cache = make empty cache
2. cache store test
   - Expected: miss.? is false
3. cache store test
   - Expected: hit.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = make_empty_cache()
val key = "src/mod.spl::evolving_fn"
val old_hash = make_scope_hash("original")
val new_hash = make_scope_hash("modified")
cache_store_test(cache, key, old_hash, ["REQC001"], [])
val miss = cache_lookup_test(cache, key, new_hash)
expect(miss.?).to_equal(false)
# Caller re-runs lint, gets empty result, stores fresh
cache_store_test(cache, key, new_hash, [], [])
val hit = cache_lookup_test(cache, key, new_hash)
expect(hit.?).to_equal(true)
```

</details>

### lint cache — symbol dependency tracking

#### when an entry is stored with symbol deps

#### symbol_index maps each dep to the cache key

1. var cache = make empty cache
2. cache store test
   - Expected: cache.symbol_index.has("Optimizer") is true
   - Expected: cache.symbol_index.has("LossConfig") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = make_empty_cache()
val key = "src/ml.spl::train"
val h = make_scope_hash("loss() body")
cache_store_test(cache, key, h, ["REQC002"], ["Optimizer", "LossConfig"])
expect(cache.symbol_index.has("Optimizer")).to_equal(true)
expect(cache.symbol_index.has("LossConfig")).to_equal(true)
```

</details>

#### symbol_index entry contains the cache key

1. var cache = make empty cache
2. cache store test
   - Expected: _contains_text(deps_for_grad, key) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = make_empty_cache()
val key = "src/ml.spl::backward"
val h = make_scope_hash("dangerous call")
cache_store_test(cache, key, h, ["REQC002"], ["GradScaler"])
val deps_for_grad = cache.symbol_index["GradScaler"]
expect(_contains_text(deps_for_grad, key)).to_equal(true)
```

</details>

#### when multiple scopes depend on the same symbol

#### symbol_index lists all dependent cache keys

1. var cache = make empty cache
2. cache store test
3. cache store test
   - Expected: deps.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = make_empty_cache()
val key_a = "src/a.spl::fn_a"
val key_b = "src/b.spl::fn_b"
val ha = make_scope_hash("body a")
val hb = make_scope_hash("body b")
cache_store_test(cache, key_a, ha, [], ["SharedSymbol"])
cache_store_test(cache, key_b, hb, [], ["SharedSymbol"])
val deps = cache.symbol_index["SharedSymbol"]
expect(deps.len()).to_equal(2)
```

</details>

### lint cache — symbol reference invalidation

#### when a depended-on symbol changes

#### invalidates the cache entry for the dependent scope

1. var cache = make empty cache
2. cache store test
3. cache invalidate symbol test
   - Expected: result.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = make_empty_cache()
val key = "src/risk.spl::risky"
val h = make_scope_hash("stable body")
cache_store_test(cache, key, h, ["REQC002"], ["DangerousHelper"])
# Simulate symbol change
cache_invalidate_symbol_test(cache, "DangerousHelper")
val result = cache_lookup_test(cache, key, h)
expect(result.?).to_equal(false)
```

</details>

#### symbol_index entry is removed after invalidation

1. var cache = make empty cache
2. cache store test
3. cache invalidate symbol test
   - Expected: cache.symbol_index.has("TargetSymbol") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = make_empty_cache()
val key = "src/risk.spl::risky"
val h = make_scope_hash("body")
cache_store_test(cache, key, h, [], ["TargetSymbol"])
cache_invalidate_symbol_test(cache, "TargetSymbol")
expect(cache.symbol_index.has("TargetSymbol")).to_equal(false)
```

</details>

#### unrelated entries are NOT removed

1. var cache = make empty cache
2. cache store test
3. cache store test
4. cache invalidate symbol test
   - Expected: result_b.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = make_empty_cache()
val key_a = "src/a.spl::fn_a"
val key_b = "src/b.spl::fn_b"
val ha = make_scope_hash("body a")
val hb = make_scope_hash("body b")
cache_store_test(cache, key_a, ha, [], ["SymA"])
cache_store_test(cache, key_b, hb, [], ["SymB"])
cache_invalidate_symbol_test(cache, "SymA")
val result_b = cache_lookup_test(cache, key_b, hb)
expect(result_b.?).to_equal(true)
```

</details>

#### when invalidating a symbol not in the index

#### does not crash and cache is unchanged

1. var cache = make empty cache
2. cache store test
3. cache invalidate symbol test
   - Expected: result.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = make_empty_cache()
val key = "src/stable.spl::fn"
val h = make_scope_hash("unchanged")
cache_store_test(cache, key, h, [], [])
# This must not crash
cache_invalidate_symbol_test(cache, "NonExistentSymbol")
val result = cache_lookup_test(cache, key, h)
expect(result.?).to_equal(true)
```

</details>

### lint cache — file-level invalidation

#### when a file is re-parsed with one changed declaration

#### removes the cache entry for the changed declaration

1. var cache = make empty cache
2. cache store test
3. new hashes["modified fn"] = make scope hash
4. cache invalidate file test
   - Expected: result.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = make_empty_cache()
val file = "src/changed.spl"
val key = "src/changed.spl::modified_fn"
val old_hash = make_scope_hash("old")
cache_store_test(cache, key, old_hash, ["REQC001"], [])
var new_hashes: Dict<text, i64> = {}
new_hashes["modified_fn"] = make_scope_hash("new")
cache_invalidate_file_test(cache, file, new_hashes)
val result = cache_lookup_test(cache, key, make_scope_hash("new"))
expect(result.?).to_equal(false)
```

</details>

#### leaves unchanged declarations in the cache

1. var cache = make empty cache
2. cache store test
3. cache store test
4. new hashes["changed fn"] = make scope hash
5. cache invalidate file test
   - Expected: result.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = make_empty_cache()
val file = "src/partial.spl"
val key_changed = "src/partial.spl::changed_fn"
val key_stable = "src/partial.spl::stable_fn"
val old_hash = make_scope_hash("old")
val stable_hash = make_scope_hash("stable body forever")
cache_store_test(cache, key_changed, old_hash, [], [])
cache_store_test(cache, key_stable, stable_hash, [], [])
var new_hashes: Dict<text, i64> = {}
new_hashes["changed_fn"] = make_scope_hash("new body")
new_hashes["stable_fn"] = stable_hash
cache_invalidate_file_test(cache, file, new_hashes)
val result = cache_lookup_test(cache, key_stable, stable_hash)
expect(result.?).to_equal(true)
```

</details>

#### when a changed declaration has symbol deps

#### cascades to invalidate symbol-dependent entries in other files

1. var cache = make empty cache
2. cache store test
3. cache store test
4. new hashes a["fn a"] = make scope hash
5. cache invalidate file test
   - Expected: result_b.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = make_empty_cache()
val file_a = "src/a.spl"
val key_a = "src/a.spl::fn_a"
val old_hash_a = make_scope_hash("a old")
cache_store_test(cache, key_a, old_hash_a, [], ["SharedDep"])
# Another file's entry depends on SharedDep
val key_b = "src/b.spl::fn_b"
val hash_b = make_scope_hash("b stable")
cache_store_test(cache, key_b, hash_b, [], ["SharedDep"])
# a.spl re-parses with changed fn_a
var new_hashes_a: Dict<text, i64> = {}
new_hashes_a["fn_a"] = make_scope_hash("a new")
cache_invalidate_file_test(cache, file_a, new_hashes_a)
# fn_b should also be invalidated via symbol cascade
val result_b = cache_lookup_test(cache, key_b, hash_b)
expect(result_b.?).to_equal(false)
```

</details>

### lint cache — scope hash properties

#### same content produces the same hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = make_scope_hash("fn body: pass_" + "todo no comment")
val h2 = make_scope_hash("fn body: pass_" + "todo no comment")
expect(h1).to_equal(h2)
```

</details>

#### different content produces different hashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = make_scope_hash("original body")
val h2 = make_scope_hash("modified body with extra statement")
expect(h1 == h2).to_equal(false)
```

</details>

#### empty content has a stable hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = make_scope_hash("")
val h2 = make_scope_hash("")
expect(h1).to_equal(h2)
```

</details>

#### hash combine produces different results for different orderings

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ha = hash_string_fnv("alpha")
val hb = hash_string_fnv("beta")
val combined_ab = hash_combine(ha, hb)
val combined_ba = hash_combine(hb, ha)
expect(combined_ab == combined_ba).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
