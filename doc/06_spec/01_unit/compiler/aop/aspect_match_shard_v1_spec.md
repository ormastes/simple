# Static-AOP directory match cache: how a pointcut becomes a reusable shard

> Purpose: document and pin the pure contract in `src/compiler/00.common/cache_contract/aspect_match_shard_v1.spl`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static-AOP directory match cache: how a pointcut becomes a reusable shard

Purpose: document and pin the pure contract in `src/compiler/00.common/cache_contract/aspect_match_shard_v1.spl`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/aop/aspect_match_shard_v1_spec.spl` |
| Updated | 2026-11-28 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: document and pin the pure contract in `src/compiler/00.common/cache_contract/aspect_match_shard_v1.spl`.

A directory
publishes its join-point facts under one SHA-256 facts key; a pointcut selector
(`execution(...)`, `attr(...)`, `within(...)` combined with `!`, `&`, `|` and
parentheses) is parsed once into a canonical digest; the pair names a match
shard that the compiler can reuse until either side changes. Anything the
contract cannot evaluate completely from directory facts fails closed: the
selector is `supported = false`, the shard is computed but never admitted to
the cache, and the existing weave path keeps running.

Audience: compiler engineers wiring the AOP match cache into the driver
(AW-1..AW-5) and reviewers who need to know exactly which edit dirties which
shard.

## Operator workflow

1. Run `bin/simple test test/01_unit/compiler/aop/aspect_match_shard_v1_spec.spl`.
2. Measure decision/condition coverage with
   `SIMPLE_EXECUTION_MODE=interpreter SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<f> <seed> run <this spec>`
   (doc/07_guide/infra/testing/coverage.md). The AW-0b bar is >= 95 % of
   decisions and of conditions from unit specs.

## Lifecycle

Research: doc/01_research/local/dir_tldr_aspect.md
Plan: doc/03_plan/compiler/aspect_cache/aspect_tldr_async_trace_plan.md (AW-0b)
Plan: doc/03_plan/compiler/cache/generic_aop_macro_semantic_cache_plan_2026-10-24.md (A-01..A-04)
Architecture: doc/04_architecture/compiler/aspect_dynload/typed_facet_pipeline_2026-08-22.md
Design: doc/05_design/compiler/cache/aspect_tldr_async_trace.md

## Decision inventory (decision/condition, both outcomes)

Line numbers refer to `aspect_match_shard_v1.spl` at the commit this spec
was written against. "DTO" marks a site reached only through a
hand-constructed public struct, not through `pointcut_selector_parse_v1`;
those are covered, not excluded. Five sites are worth knowing about because
they are not dead code, just not reachable from a well-formed parse: the
stale-facts key check (L363/L369) is reachable from a byte decode at
`directory_join_point_table_v3.spl:108`; L407 is an xxh3 collision
guard on a cache hit; the unknown atom form at L356 is the total-function
tail of `_node_matches`; and the `aop_digest_known_v1(f.facts_key)` condition
at L400 is redundant with the facts-key check. See
`doc/08_tracking/bug/aspect_match_shard_unknown_atom_fail_open_2026-11-28.md`.

Requirement ids map to the plan
(`doc/03_plan/compiler/aspect_cache/aspect_tldr_async_trace_plan.md`):
REQ-AOP-SHARD-A01..A04 are rows A-01..A-04 of
`doc/03_plan/compiler/cache/generic_aop_macro_semantic_cache_plan_2026-10-24.md`;
REQ-AOP-SHARD-COV is row AW-0b.

| Line | Decision | Conditions | Covering scenario |
|------|----------|------------|-------------------|
| 131 | `i > 0 and out[i-1] > v` (text insertion sort) | c1, c2 | unsorted member files / child roots |
| 142 | same, over join points by id | c1, c2 | every directory fixture (ids arrive unsorted) |
| 187 | `inventory_complete and admissible(guards)` | c1, c2 | guarded facts: evaluable vs unevaluable guard |
| 197 | `s.len() == 0` in `_is_ident` | c1 | `execution(*)` (empty prefix) |
| 199 | identifier character class (7 leaves) | a-z, A-Z, 0-9, `_` | `execution(Foo_9)`, `foo{`, `within(a-b)` |
| 201 | `not ok` | c1 | `foo{` / every identifier |
| 205 | `s.len() == 0` in `_is_path` | c1 | `within()` |
| 207-208 | path character class / `not ok` | ident, `.`, `/`, `*` | `within(a.b)`, `within(a/b/*)`, `within(a-b)` |
| 222 | `p < cs.len() and cs[p] == " "` (`_skip_ws`) | c1, c2 | `attr( x )` vs `attr(x)` |
| 237, 240, 242 | atom word scan, empty word, bare name | c1, c2 | bare `bar_close`, empty selector |
| 246 | `r < len and cs[r] != ")"` | c1, c2 | `attr(x` (unclosed) |
| 247, 249 | skip spaces / unclosed argument | c1 | `attr( x )`, `attr(x` |
| 251-258 | `execution` exact / prefix / reject; `attr` accept / reject | c1, c2 | `execution(foo*)`, `execution(foo_open)`, `execution(a.b*)`, `attr(a.b)` |
| 259-269 | `within` path checks, `/*` tree form, bad star | c1, c2 | `within(b.*)`, `within(a*)`, `within(/*)`, `within(a*b)` |
| 275-285 | `!` and parenthesised groups, inner failure, missing `)` | c1, c2 | `!call(x)`, `(call(x))`, `(attr(x)`, `(attr(x) attr(y))` |
| 289-305 | `&` / `|` loops, right operand failure | c1, c2 | `attr(x) & call(y)`, `attr(x) | call(y)` |
| 309, 310 | `_canon` atom and `not` forms | c1 | any parsed atom; `!attr(logged)` |
| 315 | `not` or `within_tree` needs the universe | c1, c2 | `!attr(logged)`, `within(b.*)`, `attr(logged)` |
| 324-332 | parse ok and fully consumed; root is an atom | c1, c2 | `foo{`, `attr(x) attr(y)`, expressions vs atoms |
| 341 | owner file has no directory | c1 | root-level `top.spl` under `within(a)` |
| 346-356 | node evaluation per op/form; unknown form falls through to false | each | selector algebra; DTO unknown form |
| 355 | `d == operand or d.starts_with(operand + "/")` | c1, c2 | `within(b.*)` over `b/z.spl` and `b/c/z.spl` |
| 359 | `not supported or kind != "forward"` | c1, c2 | unsupported selector; `inline` join point |
| 363, 369 | facts key no longer matches the facts | c1 | DTO facts carrying another directory's key |
| 382 | `_selector_matches` per join point | c1 | matching and non-matching join points in every directory fixture |
| 384 | `supported and complete and facts_current` | c1..c3 | unsupported, incomplete, tampered facts |
| 400 | cacheable: supported, complete, both digests known, key present | c1..c5 | unsupported; incomplete; DTO selector digest; DTO facts key |
| 402 | empty key | c1 | DTO facts carrying another directory's key |
| 405 | cacheable and already cached | c1, c2 | hit / first miss |
| 407 | cached digests equal the request | c1, c2 | DTO cache entry with a foreign selector / facts digest |
| 411 | not cacheable | c1 | incomplete inventory |
| 423 | static before/after only | c1..c3 | mode matrix |
| 442, 445, 447 | old-only, new-only, apply keys present and equal | c1..c3 | weave/unweave/reuse/reweave and missing apply keys |
| 476 | every digest is SHA-256 | c1 | forged facts key |
| 478 | shard complete | c1 | complete vs incomplete directory reads |
| 509-516 | unsupported, incomplete directory, universe proof | c1..c3 | universe scenarios |
| 557 | 1..3 digests per side | c1..c4 | empty and oversized digest tables |

Exclusions: none. Match arms (`case Some` / `case None`) are not decisions
under the interpreter's coverage semantics; their `None` sides are still
exercised (`pointcut_local_key_from_hex_v1("")`, forged digests).

## Compatibility and limitations

Pure value contract: no file system, clock, or process access, so results are
identical on every host. Publication and single-flight live in the driver and
are out of scope here.

## Scenarios

### DirectoryJoinPointFactsV1

#### sorts join points, records a completeness witness and a stable key

- Build directory a from three join points given out of id order
- Read back the sorted ids and the SHA-256 facts key
   - Exec capture: after_step
   - Evidence: execution result verified by 6 expected checks
   - Expected: f.sorted_join_points[0].id equals `a/x.spl::bar_close`
   - Expected: f.sorted_join_points[2].id equals `a/y.spl::foo_read`
   - Expected: f.complete is true
   - Expected: f.facts_key equals `directory_facts_key_v1(dir_a([]))`
   - Expected: f.facts_key.len() equals `71)  # oracle: "sha256:" (7 chars) + 64 lower-hex digits`
   - Expected: f.facts_key.starts_with("sha256:") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A03
step("Build directory a from three join points given out of id order")
val f = dir_a([])
step("Read back the sorted ids and the SHA-256 facts key")
expect(f.sorted_join_points[0].id).to_equal("a/x.spl::bar_close")
expect(f.sorted_join_points[2].id).to_equal("a/y.spl::foo_read")
expect(f.complete).to_equal(true)
expect(f.facts_key).to_equal(directory_facts_key_v1(dir_a([])))
expect(f.facts_key.len()).to_equal(71)  # oracle: "sha256:" (7 chars) + 64 lower-hex digits
expect(f.facts_key.starts_with("sha256:")).to_equal(true)
```

</details>

#### sorts member files and child roots so listing order never changes the key

- Build the same directory twice, once with member files and child roots reversed
- Both builds carry the same sorted lists and therefore the same facts key
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: reversed.sorted_member_files equals `["a/x.spl", "a/y.spl"]`
   - Expected: reversed.sorted_child_roots equals `["root-1", "root-2"]`
   - Expected: reversed.facts_key equals `forward.facts_key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-COV
step("Build the same directory twice, once with member files and child roots reversed")
val points = [jp("a/x.spl", "foo_open", ["logged"], "b1")]
val forward = directory_join_point_facts_v1("a", ["a/x.spl", "a/y.spl"], points,
    ["root-1", "root-2"], true)
val reversed = directory_join_point_facts_v1("a", ["a/y.spl", "a/x.spl"], points,
    ["root-2", "root-1"], true)
step("Both builds carry the same sorted lists and therefore the same facts key")
expect(reversed.sorted_member_files).to_equal(["a/x.spl", "a/y.spl"])
expect(reversed.sorted_child_roots).to_equal(["root-1", "root-2"])
expect(reversed.facts_key).to_equal(forward.facts_key)
```

</details>

#### an unevaluable @when guard makes the directory incomplete

- Build guard roots from one evaluable and one unevaluable guard evaluation
- Only the evaluable root keeps the inventory complete; the guard root enters the key
   - Exec capture: after_step
   - Evidence: execution result verified by 5 expected checks
   - Expected: guarded.complete is true
   - Expected: blocked.complete is false
   - Expected: guarded.active_guard_root equals `good.root_digest`
   - Expected: guarded.facts_key == plain.facts_key is false
   - Expected: r.cacheable is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A04
step("Build guard roots from one evaluable and one unevaluable guard evaluation")
val good = active_guard_root_v1("windows/x86_64",
    [GuardEvalV1(guard: guard_id_v1("when", "os=\"windows\""), evaluable: true, active: true)])
val bad = active_guard_root_v1("windows/x86_64",
    [GuardEvalV1(guard: guard_id_v1("when", "flavor=\"x\""), evaluable: false, active: false)])
val points = [jp("a/x.spl", "foo_open", ["logged"], "b1")]
val guarded = directory_join_point_facts_guarded_v1("a", ["a/x.spl"], points, [], true, good)
val blocked = directory_join_point_facts_guarded_v1("a", ["a/x.spl"], points, [], true, bad)
val plain = directory_join_point_facts_v1("a", ["a/x.spl"], points, [], true)
step("Only the evaluable root keeps the inventory complete; the guard root enters the key")
expect(guarded.complete).to_equal(true)
expect(blocked.complete).to_equal(false)
expect(guarded.active_guard_root).to_equal(good.root_digest)
expect(guarded.facts_key == plain.facts_key).to_equal(false)
val r = pointcut_match_cache_acquire_v1(pointcut_match_cache_new_v1(),
    pointcut_selector_parse_v1("attr(logged)"), blocked)
expect(r.cacheable).to_equal(false)
```

</details>

### A-01 advice body edit

#### reuses the match shard and dirties only matched join points

- Acquire the attr(logged) shard for directory a on an empty cache
   - Expected: sel.supported is true
   - Expected: r1.hit is false
   - Expected: r1.shard.sorted_matching_ids equals `["a/x.spl::foo_open"]`
- Edit only the advice body and acquire again
- The shard is a hit with one computation; only foo_open is rewoven
   - Exec capture: after_step
   - Evidence: execution result verified by 6 expected checks
   - Expected: r2.hit is true
   - Expected: r2.cache.computations equals `1)  # oracle: the first acquire was the only computation`
   - Expected: d.reweave equals `["a/x.spl::foo_open"]`
   - Expected: d.weave equals `[]`
   - Expected: d.unweave equals `[]`
   - Expected: d.reuse equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A01
step("Acquire the attr(logged) shard for directory a on an empty cache")
val sel = pointcut_selector_parse_v1("attr(logged)")
expect(sel.supported).to_equal(true)
val facts = dir_a([])
val c0 = pointcut_match_cache_new_v1()
val r1 = pointcut_match_cache_acquire_v1(c0, sel, facts)
expect(r1.hit).to_equal(false)
expect(r1.shard.sorted_matching_ids).to_equal(["a/x.spl::foo_open"])
val old_keys = apply_keys(r1.cache, r1.key, advice("body_v1"), facts)
step("Edit only the advice body and acquire again")
val r2 = pointcut_match_cache_acquire_v1(r1.cache, sel, facts)
step("The shard is a hit with one computation; only foo_open is rewoven")
expect(r2.hit).to_equal(true)
expect(r2.cache.computations).to_equal(1)  # oracle: the first acquire was the only computation
val new_keys = apply_keys(r2.cache, r2.key, advice("body_v2"), facts)
val d = aspect_weave_plan_delta_v1(r1.shard, old_keys, r2.shard, new_keys)
expect(d.reweave).to_equal(["a/x.spl::foo_open"])
expect(d.weave).to_equal([])
expect(d.unweave).to_equal([])
expect(d.reuse).to_equal([])
```

</details>

#### keeps every woven object when advice facets are unchanged

- Compute apply keys once and diff the shard against itself
- Every matched join point is reused and nothing is rewoven
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: d.reuse equals `["a/x.spl::foo_open"]`
   - Expected: d.reweave equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A01
step("Compute apply keys once and diff the shard against itself")
val sel = pointcut_selector_parse_v1("attr(logged)")
val facts = dir_a([])
val r1 = pointcut_match_cache_acquire_v1(pointcut_match_cache_new_v1(), sel, facts)
val k = apply_keys(r1.cache, r1.key, advice("body_v1"), facts)
val d = aspect_weave_plan_delta_v1(r1.shard, k, r1.shard, k)
step("Every matched join point is reused and nothing is rewoven")
expect(d.reuse).to_equal(["a/x.spl::foo_open"])
expect(d.reweave).to_equal([])
```

</details>

#### reweaves a matched join point whose apply key is missing on either side

- Diff a shard against itself with the old, then the new, apply-key table empty
- An absent apply key can never prove reuse, so the join point is rewoven
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: no_old.reweave equals `["a/x.spl::foo_open"]`
   - Expected: no_new.reweave equals `["a/x.spl::foo_open"]`
   - Expected: no_new.reuse equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-COV
step("Diff a shard against itself with the old, then the new, apply-key table empty")
val sel = pointcut_selector_parse_v1("attr(logged)")
val facts = dir_a([])
val r1 = pointcut_match_cache_acquire_v1(pointcut_match_cache_new_v1(), sel, facts)
val k = apply_keys(r1.cache, r1.key, advice("body_v1"), facts)
val none: Dict<text, text> = {}
val no_old = aspect_weave_plan_delta_v1(r1.shard, none, r1.shard, k)
val no_new = aspect_weave_plan_delta_v1(r1.shard, k, r1.shard, none)
step("An absent apply key can never prove reuse, so the join point is rewoven")
expect(no_old.reweave).to_equal(["a/x.spl::foo_open"])
expect(no_new.reweave).to_equal(["a/x.spl::foo_open"])
expect(no_new.reuse).to_equal([])
```

</details>

#### selector digest excludes advice body while apply key includes it

- Derive apply keys that differ only in advice body or only in base body
- The selector digest and match key ignore the advice body; each body change yields a distinct apply key
   - Exec capture: after_step
   - Evidence: execution result verified by 4 expected checks
   - Expected: shard_x.selector_digest equals `shard_y.selector_digest`
   - Expected: shard_x.match_digest equals `shard_y.match_digest`
   - Expected: a == b is false
   - Expected: a == c is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A01
step("Derive apply keys that differ only in advice body or only in base body")
val a = advice_apply_key_v1("m", advice("x"), "b1")
val b = advice_apply_key_v1("m", advice("y"), "b1")
val c = advice_apply_key_v1("m", advice("x"), "b9")
step("The selector digest and match key ignore the advice body; each body change yields a distinct apply key")
val sel = pointcut_selector_parse_v1("attr(logged)")
val facts = dir_a([])
val shard_x = pointcut_match_shard_compute_v1(sel, facts)
val shard_y = pointcut_match_shard_compute_v1(pointcut_selector_parse_v1("attr(logged)"), facts)
expect(shard_x.selector_digest).to_equal(shard_y.selector_digest)
expect(shard_x.match_digest).to_equal(shard_y.match_digest)
expect(a == b).to_equal(false)
expect(a == c).to_equal(false)
```

</details>

### A-02 selector change

#### unweaves old-only and weaves new-only join points

- Acquire execution(foo*) and then execution(bar*) over directory a
   - Expected: r1.shard.sorted_matching_ids equals `["a/x.spl::foo_open", "a/y.spl::foo_read"]`
   - Expected: r2.hit is false
- The foo_* join points are unwoven and bar_close is woven
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: d.unweave equals `["a/x.spl::foo_open", "a/y.spl::foo_read"]`
   - Expected: d.weave equals `["a/x.spl::bar_close"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A02
step("Acquire execution(foo*) and then execution(bar*) over directory a")
val facts = dir_a([])
val s_old = pointcut_selector_parse_v1("execution(foo*)")
val s_new = pointcut_selector_parse_v1("execution(bar*)")
val r1 = pointcut_match_cache_acquire_v1(pointcut_match_cache_new_v1(), s_old, facts)
expect(r1.shard.sorted_matching_ids).to_equal(["a/x.spl::foo_open", "a/y.spl::foo_read"])
val r2 = pointcut_match_cache_acquire_v1(r1.cache, s_new, facts)
expect(r2.hit).to_equal(false)
val d = aspect_weave_plan_delta_v1(r1.shard, apply_keys(r1.cache, r1.key, advice("v"), facts),
    r2.shard, apply_keys(r2.cache, r2.key, advice("v"), facts))
step("The foo_* join points are unwoven and bar_close is woven")
expect(d.unweave).to_equal(["a/x.spl::foo_open", "a/y.spl::foo_read"])
expect(d.weave).to_equal(["a/x.spl::bar_close"])
```

</details>

#### exact-name selector keeps the existing forward-selector semantics

- Match the bare name bar_close and its execution(bar_close) spelling
- Both spellings are the same exact atom and select only bar_close
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: bare.form equals `exact`
   - Expected: spelled.selector_digest equals `bare.selector_digest`
   - Expected: ids(dir_a([]), "bar_close") equals `["a/x.spl::bar_close"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A02
step("Match the bare name bar_close and its execution(bar_close) spelling")
val bare = pointcut_selector_parse_v1("bar_close")
val spelled = pointcut_selector_parse_v1("execution(bar_close)")
step("Both spellings are the same exact atom and select only bar_close")
expect(bare.form).to_equal("exact")
expect(spelled.selector_digest).to_equal(bare.selector_digest)
expect(ids(dir_a([]), "bar_close")).to_equal(["a/x.spl::bar_close"])
```

</details>

### A-03 add/rename function with attr

#### changes the owning directory facts key and misses only that shard

- Cache attr(logged) shards for directories a and b, then add foo_write to a
   - Expected: grown.facts_key == dir_a([]).facts_key is false
- Directory a misses and gains foo_write; directory b is still a hit
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: r_a2.hit is false
   - Expected: r_a2.shard.sorted_matching_ids equals `["a/x.spl::foo_open", "a/y.spl::foo_write"]`
   - Expected: r_b2.hit is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A03
step("Cache attr(logged) shards for directories a and b, then add foo_write to a")
val sel = pointcut_selector_parse_v1("attr(logged)")
val r_a = pointcut_match_cache_acquire_v1(pointcut_match_cache_new_v1(), sel, dir_a([]))
val r_b = pointcut_match_cache_acquire_v1(r_a.cache, sel, dir_b())
val grown = dir_a([jp("a/y.spl", "foo_write", ["logged"], "b5")])
expect(grown.facts_key == dir_a([]).facts_key).to_equal(false)
val r_a2 = pointcut_match_cache_acquire_v1(r_b.cache, sel, grown)
step("Directory a misses and gains foo_write; directory b is still a hit")
expect(r_a2.hit).to_equal(false)
expect(r_a2.shard.sorted_matching_ids).to_equal(["a/x.spl::foo_open", "a/y.spl::foo_write"])
val r_b2 = pointcut_match_cache_acquire_v1(r_a2.cache, sel, dir_b())
expect(r_b2.hit).to_equal(true)
```

</details>

#### a rename invalidates the negative root (old id unwoven, new id woven)

- Rename foo_open to foo_opened inside directory a
   - Expected: renamed.negative_root == before.negative_root is false
- The old id is unwoven and the new id is woven
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: d.unweave equals `["a/x.spl::foo_open"]`
   - Expected: d.weave equals `["a/x.spl::foo_opened"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A03
step("Rename foo_open to foo_opened inside directory a")
val sel = pointcut_selector_parse_v1("attr(logged)")
val before = dir_a([])
val renamed = directory_join_point_facts_v1("a", ["a/x.spl", "a/y.spl"],
    [jp("a/x.spl", "foo_opened", ["logged"], "b1"), jp("a/x.spl", "bar_close", [], "b2"),
     jp("a/y.spl", "foo_read", [], "b3")], [], true)
expect(renamed.negative_root == before.negative_root).to_equal(false)
val r1 = pointcut_match_cache_acquire_v1(pointcut_match_cache_new_v1(), sel, before)
val r2 = pointcut_match_cache_acquire_v1(r1.cache, sel, renamed)
val d = aspect_weave_plan_delta_v1(r1.shard, apply_keys(r1.cache, r1.key, advice("v"), before),
    r2.shard, apply_keys(r2.cache, r2.key, advice("v"), renamed))
step("The old id is unwoven and the new id is woven")
expect(d.unweave).to_equal(["a/x.spl::foo_open"])
expect(d.weave).to_equal(["a/x.spl::foo_opened"])
```

</details>

#### child directory root change changes the parent facts key

- Build parent p over child a, then over child a with one more join point
- The parent facts key follows the child root
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: p1.facts_key == p2.facts_key is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A03
step("Build parent p over child a, then over child a with one more join point")
val p1 = directory_join_point_facts_v1("p", [], [], [dir_a([]).facts_key], true)
val p2 = directory_join_point_facts_v1("p", [], [],
    [dir_a([jp("a/y.spl", "z", [], "b")]).facts_key], true)
step("The parent facts key follows the child root")
expect(p1.facts_key == p2.facts_key).to_equal(false)
```

</details>

### A-04 conservative fallback

#### rejects unsupported selectors and incomplete inventories as non-cacheable

- Parse selectors the static facts cannot answer, and acquire over an incomplete inventory
   - Expected: shape("call(foo)") equals `REJECTED`
   - Expected: shape("attr(x) &") equals `REJECTED`
   - Expected: shape("within(a*)") equals `REJECTED`
- The acquire is not cacheable and the cache stays empty
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: r.cacheable is false
   - Expected: r.cache.shards.len() equals `0)  # oracle: nothing may be admitted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A04
step("Parse selectors the static facts cannot answer, and acquire over an incomplete inventory")
expect(shape("call(foo)")).to_equal(REJECTED)
expect(shape("attr(x) &")).to_equal(REJECTED)
expect(shape("within(a*)")).to_equal(REJECTED)
val inc = directory_join_point_facts_v1("a", ["a/x.spl"], [], [], false)
val r = pointcut_match_cache_acquire_v1(pointcut_match_cache_new_v1(),
    pointcut_selector_parse_v1("attr(logged)"), inc)
step("The acquire is not cacheable and the cache stays empty")
expect(r.cacheable).to_equal(false)
expect(r.cache.shards.len()).to_equal(0)  # oracle: nothing may be admitted
```

</details>

#### computes an unsupported selector over complete facts but never admits it

- Acquire call(foo) over the complete directory a
- A key exists, but the shard matches nothing, is incomplete and is not admitted
   - Exec capture: after_step
   - Evidence: execution result verified by 5 expected checks
   - Expected: r.key.starts_with("xxh3-128:") is true
   - Expected: r.cacheable is false
   - Expected: r.shard.sorted_matching_ids equals `[]`
   - Expected: r.shard.complete is false
   - Expected: r.cache.computations equals `0)  # oracle: a non-admitted compute is not counted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A04
step("Acquire call(foo) over the complete directory a")
val sel = pointcut_selector_parse_v1("call(foo)")
val r = pointcut_match_cache_acquire_v1(pointcut_match_cache_new_v1(), sel, dir_a([]))
step("A key exists, but the shard matches nothing, is incomplete and is not admitted")
expect(r.key.starts_with("xxh3-128:")).to_equal(true)
expect(r.cacheable).to_equal(false)
expect(r.shard.sorted_matching_ids).to_equal([])
expect(r.shard.complete).to_equal(false)
expect(r.cache.computations).to_equal(0)  # oracle: a non-admitted compute is not counted
```

</details>

#### only static before/after advice is cacheable

- Classify each advice mode and activation
- Only static before and static after are cacheable
   - Exec capture: after_step
   - Evidence: execution result verified by 4 expected checks
   - Expected: aspect_advice_mode_cacheable_v1("before", "static") is true
   - Expected: aspect_advice_mode_cacheable_v1("after", "static") is true
   - Expected: aspect_advice_mode_cacheable_v1("around", "static") is false
   - Expected: aspect_advice_mode_cacheable_v1("before", "dynload") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A04
step("Classify each advice mode and activation")
step("Only static before and static after are cacheable")
expect(aspect_advice_mode_cacheable_v1("before", "static")).to_equal(true)
expect(aspect_advice_mode_cacheable_v1("after", "static")).to_equal(true)
expect(aspect_advice_mode_cacheable_v1("around", "static")).to_equal(false)
expect(aspect_advice_mode_cacheable_v1("before", "dynload")).to_equal(false)
```

</details>

### pointcut selector grammar

#### accepts each documented atom form with its canonical form name

- Parse one selector per atom form
- Each atom reports its form and operand; dots in within() become slashes
   - Exec capture: after_step
   - Evidence: execution result verified by 12 expected checks
   - Expected: exact.form equals `exact`
   - Expected: exact.operand equals `Foo_9`
   - Expected: prefix.form equals `prefix`
   - Expected: prefix.operand equals `foo`
   - Expected: attr.form equals `attr`
   - Expected: attr.operand equals `Zed`
   - Expected: within.form equals `within`
   - Expected: within.operand equals `a/b`
   - Expected: tree.form equals `within_tree`
   - Expected: tree.operand equals `a/b`
   - Expected: tree.needs_universe is true
   - Expected: attr.needs_universe is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-COV
step("Parse one selector per atom form")
val exact = pointcut_selector_parse_v1("execution(Foo_9)")
val prefix = pointcut_selector_parse_v1("execution(foo*)")
val attr = pointcut_selector_parse_v1("attr( Zed )")
val within = pointcut_selector_parse_v1("within(a.b)")
val tree = pointcut_selector_parse_v1("within(a/b/*)")
step("Each atom reports its form and operand; dots in within() become slashes")
expect(exact.form).to_equal("exact")
expect(exact.operand).to_equal("Foo_9")
expect(prefix.form).to_equal("prefix")
expect(prefix.operand).to_equal("foo")
expect(attr.form).to_equal("attr")
expect(attr.operand).to_equal("Zed")
expect(within.form).to_equal("within")
expect(within.operand).to_equal("a/b")
expect(tree.form).to_equal("within_tree")
expect(tree.operand).to_equal("a/b")
expect(tree.needs_universe).to_equal(true)
expect(attr.needs_universe).to_equal(false)
```

</details>

#### fails closed on malformed atoms

- Parse atoms with an empty, unclosed, or out-of-alphabet argument
- Every one is unsupported with no nodes and a universe requirement
   - Exec capture: after_step
   - Evidence: execution result verified by 10 expected checks
   - Expected: shape("") equals `REJECTED`
   - Expected: shape("attr(x") equals `REJECTED`
   - Expected: shape("attr(a.b)") equals `REJECTED`
   - Expected: shape("execution(*)") equals `REJECTED`
   - Expected: shape("execution(a.b*)") equals `REJECTED`
   - Expected: shape("execution(a.b)") equals `REJECTED`
   - Expected: shape("within()") equals `REJECTED`
   - Expected: shape("within(a-b)") equals `REJECTED`
   - Expected: shape("within(/*)") equals `REJECTED`
   - Expected: shape("within(a*b)") equals `REJECTED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A04
step("Parse atoms with an empty, unclosed, or out-of-alphabet argument")
step("Every one is unsupported with no nodes and a universe requirement")
expect(shape("")).to_equal(REJECTED)
expect(shape("attr(x")).to_equal(REJECTED)
expect(shape("attr(a.b)")).to_equal(REJECTED)
expect(shape("execution(*)")).to_equal(REJECTED)
expect(shape("execution(a.b*)")).to_equal(REJECTED)
expect(shape("execution(a.b)")).to_equal(REJECTED)
expect(shape("within()")).to_equal(REJECTED)
expect(shape("within(a-b)")).to_equal(REJECTED)
expect(shape("within(/*)")).to_equal(REJECTED)
expect(shape("within(a*b)")).to_equal(REJECTED)
```

</details>

#### fails closed on malformed expressions

- Parse operators whose operand is unsupported, unbalanced groups and trailing text
- Every one is unsupported; a valid prefix never leaks a partial selector
   - Exec capture: after_step
   - Evidence: execution result verified by 8 expected checks
   - Expected: shape("!call(x)") equals `REJECTED`
   - Expected: shape("(call(x))") equals `REJECTED`
   - Expected: shape("(attr(x)") equals `REJECTED`
   - Expected: shape("(attr(x) attr(y))") equals `REJECTED`
   - Expected: shape("attr(x) & call(y)") equals `REJECTED`
   - Expected: shape("attr(x) | call(y)") equals `REJECTED`
   - Expected: shape("attr(x) attr(y)") equals `REJECTED`
   - Expected: shape("foo{") equals `REJECTED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A04
step("Parse operators whose operand is unsupported, unbalanced groups and trailing text")
step("Every one is unsupported; a valid prefix never leaks a partial selector")
expect(shape("!call(x)")).to_equal(REJECTED)
expect(shape("(call(x))")).to_equal(REJECTED)
expect(shape("(attr(x)")).to_equal(REJECTED)
expect(shape("(attr(x) attr(y))")).to_equal(REJECTED)
expect(shape("attr(x) & call(y)")).to_equal(REJECTED)
expect(shape("attr(x) | call(y)")).to_equal(REJECTED)
expect(shape("attr(x) attr(y)")).to_equal(REJECTED)
expect(shape("foo{")).to_equal(REJECTED)
```

</details>

### A-04 selector algebra

#### evaluates ! & | and parentheses over a complete directory

- Evaluate negation, conjunction and a parenthesised disjunction over directory a
- Each expression selects exactly the join points its algebra names
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: ids(f, "!attr(logged)") equals `["a/x.spl::bar_close", "a/y.spl::foo_read"]`
   - Expected: ids(f, "execution(foo*) & !attr(logged)") equals `["a/y.spl::foo_read"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A04
step("Evaluate negation, conjunction and a parenthesised disjunction over directory a")
val f = dir_a([])
step("Each expression selects exactly the join points its algebra names")
expect(ids(f, "!attr(logged)")).to_equal(["a/x.spl::bar_close", "a/y.spl::foo_read"])
expect(ids(f, "execution(foo*) & !attr(logged)")).to_equal(["a/y.spl::foo_read"])
expect(ids(f, "(bar_close | attr(logged)) & within(a)")).to_equal(
    ["a/x.spl::bar_close", "a/x.spl::foo_open"])
```

</details>

#### selector digest is canonical over whitespace and distinguishes operators

- Parse the same expression with and without spaces, and with | for &
- Whitespace does not change the digest; the operator does
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: a.selector_digest equals `b.selector_digest`
   - Expected: a.form equals `expr`
   - Expected: a.selector_digest == c.selector_digest is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A04
step("Parse the same expression with and without spaces, and with | for &")
val a = pointcut_selector_parse_v1("attr(x)&!foo")
val b = pointcut_selector_parse_v1(" attr( x ) & ! foo ")
val c = pointcut_selector_parse_v1("attr(x)|!foo")
step("Whitespace does not change the digest; the operator does")
expect(a.selector_digest).to_equal(b.selector_digest)
expect(a.form).to_equal("expr")
expect(a.selector_digest == c.selector_digest).to_equal(false)
```

</details>

#### only forward join points are selectable

- Add an inline join point carrying the logged attribute to directory a
- attr(logged) still selects only the forward join point
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: ids(f, "attr(logged)") equals `["a/x.spl::foo_open"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-COV
step("Add an inline join point carrying the logged attribute to directory a")
val f = dir_a([JoinPointFactV1(id: "a/x.spl::inl", kind: "inline", symbol: "inl",
    attrs: ["logged"], owner_file: "a/x.spl", base_body_digest: "b9")])
step("attr(logged) still selects only the forward join point")
expect(ids(f, "attr(logged)")).to_equal(["a/x.spl::foo_open"])
```

</details>

#### within() matches the owner directory and within(x.*) the whole subtree

- Build a directory with a root-level file, a b/ file and a nested b/c/ file
- within(b) is one directory; within(b.*) adds b/c but not the sibling bc/
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: ids(f, "within(b)") equals `["b/z.spl::z"]`
   - Expected: ids(f, "within(b.*)") equals `["b/c/z.spl::deep", "b/z.spl::z"]`
   - Expected: ids(f, "within(a)") equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-COV
step("Build a directory with a root-level file, a b/ file and a nested b/c/ file")
val f = directory_join_point_facts_v1("mixed", ["top.spl", "b/z.spl", "b/c/z.spl"],
    [jp("top.spl", "t", [], "b1"), jp("b/z.spl", "z", [], "b2"), jp("b/c/z.spl", "deep", [], "b3"),
     jp("bc/q.spl", "near", [], "b4")], [], true)
step("within(b) is one directory; within(b.*) adds b/c but not the sibling bc/")
expect(ids(f, "within(b)")).to_equal(["b/z.spl::z"])
expect(ids(f, "within(b.*)")).to_equal(["b/c/z.spl::deep", "b/z.spl::z"])
expect(ids(f, "within(a)")).to_equal([])
```

</details>

#### a hand-built selector node with an unknown form matches nothing

- Construct a supported selector whose only atom has a form the evaluator does not know
- The evaluator falls through to false for every join point
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: shard.complete is true
   - Expected: shard.sorted_matching_ids equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-COV
step("Construct a supported selector whose only atom has a form the evaluator does not know")
val known = pointcut_selector_parse_v1("attr(logged)")
val odd = PointcutSelectorV1(source: "mystery", form: "mystery", operand: "m", supported: true,
    nodes: [PointcutSelNodeV1(op: "atom", form: "mystery", operand: "m", left: -1, right: -1)],
    root: 0, needs_universe: false, selector_digest: known.selector_digest)
val shard = pointcut_match_shard_compute_v1(odd, dir_a([]))
step("The evaluator falls through to false for every join point")
# LATENT FAIL-OPEN: this shard is complete = true although the atom was never evaluated; today only the parser builds selectors so the form cannot occur, but AW-3 builds selectors outside the parser. Filed: doc/08_tracking/bug/aspect_match_shard_unknown_atom_fail_open_2026-11-28.md
expect(shard.complete).to_equal(true)
expect(shard.sorted_matching_ids).to_equal([])
```

</details>

#### negation over an incomplete directory is not cacheable

- Acquire !attr(test) over an incomplete inventory
- The result is computed but not cacheable
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: r.cacheable is false
   - Expected: r.shard.complete is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A04
step("Acquire !attr(test) over an incomplete inventory")
val inc = directory_join_point_facts_v1("a", ["a/x.spl"],
    [jp("a/x.spl", "foo_open", [], "b1")], [], false)
val r = pointcut_match_cache_acquire_v1(pointcut_match_cache_new_v1(),
    pointcut_selector_parse_v1("!attr(test)"), inc)
step("The result is computed but not cacheable")
expect(r.cacheable).to_equal(false)
expect(r.shard.complete).to_equal(false)
```

</details>

### cross-directory universe

#### cross-directory within/negation needs a proven complete universe

- Evaluate within(b.*) | !attr(logged) over a and b, without and with a universe proof
   - Expected: sel.needs_universe is true
- Without the proof the union is conservative; with it the union is complete
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: partial.complete is false
   - Expected: partial.reason equals `universe-incomplete`
   - Expected: full.complete is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A04
step("Evaluate within(b.*) | !attr(logged) over a and b, without and with a universe proof")
val sel = pointcut_selector_parse_v1("within(b.*) | !attr(logged)")
expect(sel.needs_universe).to_equal(true)
val partial = pointcut_match_universe_v1(sel, [dir_a([]), dir_b()], false)
val full = pointcut_match_universe_v1(sel, [dir_a([]), dir_b()], true)
step("Without the proof the union is conservative; with it the union is complete")
expect(partial.complete).to_equal(false)
expect(partial.reason).to_equal("universe-incomplete")
expect(full.complete).to_equal(true)
expect(full.sorted_matching_ids).to_equal(
    ["a/x.spl::bar_close", "a/y.spl::foo_read", "b/z.spl::bar_open"])
```

</details>

#### positive-only selectors are complete without a universe proof

- Evaluate attr(logged) over a and b with no universe proof
- The union is complete and sorted
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: r.complete is true
   - Expected: r.sorted_matching_ids equals `["a/x.spl::foo_open", "b/z.spl::bar_open"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A04
step("Evaluate attr(logged) over a and b with no universe proof")
val r = pointcut_match_universe_v1(pointcut_selector_parse_v1("attr(logged)"),
    [dir_a([]), dir_b()], false)
step("The union is complete and sorted")
expect(r.complete).to_equal(true)
expect(r.sorted_matching_ids).to_equal(["a/x.spl::foo_open", "b/z.spl::bar_open"])
```

</details>

#### names the first incomplete directory and reports unsupported selectors first

- Evaluate a supported selector over two incomplete directories, then call(foo) over a
- The reason names only the first incomplete scope; an unsupported selector wins over all
   - Exec capture: after_step
   - Evidence: execution result verified by 5 expected checks
   - Expected: two.complete is false
   - Expected: two.reason equals `incomplete-directory:p`
   - Expected: two.sorted_matching_ids equals `["p/x.spl::foo_open", "q/x.spl::foo_open"]`
   - Expected: unsupported.complete is false
   - Expected: unsupported.reason equals `unsupported-selector`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-COV
step("Evaluate a supported selector over two incomplete directories, then call(foo) over a")
val two = pointcut_match_universe_v1(pointcut_selector_parse_v1("attr(logged)"),
    [incomplete_dir("p"), incomplete_dir("q")], true)
val unsupported = pointcut_match_universe_v1(pointcut_selector_parse_v1("call(foo)"),
    [dir_a([])], false)
step("The reason names only the first incomplete scope; an unsupported selector wins over all")
expect(two.complete).to_equal(false)
expect(two.reason).to_equal("incomplete-directory:p")
expect(two.sorted_matching_ids).to_equal(["p/x.spl::foo_open", "q/x.spl::foo_open"])
expect(unsupported.complete).to_equal(false)
expect(unsupported.reason).to_equal("unsupported-selector")
```

</details>

### match cache admission

#### a facts record whose key no longer matches its facts has no key or identity

- Present directory a carrying directory b's facts key
- Key and identity are empty, the shard is incomplete and nothing is admitted
   - Exec capture: after_step
   - Evidence: execution result verified by 6 expected checks
   - Expected: pointcut_match_key_v1(sel, f) equals ``
   - Expected: pointcut_match_identity_v1(sel, f) equals ``
   - Expected: r.key equals ``
   - Expected: r.cacheable is false
   - Expected: r.shard.complete is false
   - Expected: r.shard.sorted_matching_ids equals `["a/x.spl::foo_open"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A04
step("Present directory a carrying directory b's facts key")
val sel = pointcut_selector_parse_v1("attr(logged)")
val f = tampered_dir_a()
val r = pointcut_match_cache_acquire_v1(pointcut_match_cache_new_v1(), sel, f)
step("Key and identity are empty, the shard is incomplete and nothing is admitted")
expect(pointcut_match_key_v1(sel, f)).to_equal("")
expect(pointcut_match_identity_v1(sel, f)).to_equal("")
expect(r.key).to_equal("")
expect(r.cacheable).to_equal(false)
expect(r.shard.complete).to_equal(false)
expect(r.shard.sorted_matching_ids).to_equal(["a/x.spl::foo_open"])
```

</details>

#### a selector digest under a fast algorithm is never admitted

- Relabel the attr(logged) selector digest as xxh3-128 and acquire
- The acquire is a non-cacheable miss and the cache stays empty
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: r.cacheable is false
   - Expected: r.hit is false
   - Expected: r.cache.shards.len() equals `0)  # oracle: nothing may be admitted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A04
step("Relabel the attr(logged) selector digest as xxh3-128 and acquire")
val good = pointcut_selector_parse_v1("attr(logged)")
val hex = good.selector_digest.slice(7, good.selector_digest.len())
val fast = PointcutSelectorV1(..good, selector_digest: "xxh3-128:" + hex)
val r = pointcut_match_cache_acquire_v1(pointcut_match_cache_new_v1(), fast, dir_a([]))
step("The acquire is a non-cacheable miss and the cache stays empty")
expect(r.cacheable).to_equal(false)
expect(r.hit).to_equal(false)
expect(r.cache.shards.len()).to_equal(0)  # oracle: nothing may be admitted
```

</details>

#### recomputes instead of serving a cached shard recorded for another selector or directory

- Seed the cache key of (attr(logged), a) with shards naming a foreign selector, then a foreign directory
- Both are misses that recompute and replace the stale entry with the correct shard
   - Exec capture: after_step
   - Evidence: execution result verified by 5 expected checks
   - Expected: r_sel.hit is false
   - Expected: r_dir.hit is false
   - Expected: r_sel.cache.computations equals `2)  # oracle: seeded count 1 plus this recompute`
   - Expected: r_sel.cache.shards[r1.key].selector_digest equals `sel.selector_digest`
   - Expected: r_dir.cache.shards[r1.key].dir_facts_key equals `f.facts_key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A04
step("Seed the cache key of (attr(logged), a) with shards naming a foreign selector, then a foreign directory")
val sel = pointcut_selector_parse_v1("attr(logged)")
val f = dir_a([])
val r1 = pointcut_match_cache_acquire_v1(pointcut_match_cache_new_v1(), sel, f)
val foreign_sel = PointcutMatchShardV1(..r1.shard,
    selector_digest: pointcut_selector_parse_v1("attr(other)").selector_digest)
val foreign_dir = PointcutMatchShardV1(..r1.shard, dir_facts_key: dir_b().facts_key)
val r_sel = pointcut_match_cache_acquire_v1(single_shard_cache(r1.key, foreign_sel), sel, f)
val r_dir = pointcut_match_cache_acquire_v1(single_shard_cache(r1.key, foreign_dir), sel, f)
step("Both are misses that recompute and replace the stale entry with the correct shard")
expect(r_sel.hit).to_equal(false)
expect(r_dir.hit).to_equal(false)
expect(r_sel.cache.computations).to_equal(2)  # oracle: seeded count 1 plus this recompute
expect(r_sel.cache.shards[r1.key].selector_digest).to_equal(sel.selector_digest)
expect(r_dir.cache.shards[r1.key].dir_facts_key).to_equal(f.facts_key)
```

</details>

#### the in-process key is xxh3-128 tagged, and malformed hex yields no key

- Derive the local key for a real pair and from malformed hex
- Valid hex round-trips to the same key; empty or non-hex input gives none
   - Exec capture: after_step
   - Evidence: execution result verified by 4 expected checks
   - Expected: r.key.starts_with("xxh3-128:") is true
   - Expected: pointcut_local_key_from_hex_v1(hex) equals `r.key`
   - Expected: pointcut_local_key_from_hex_v1("") equals ``
   - Expected: pointcut_local_key_from_hex_v1("not-hex") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-COV
step("Derive the local key for a real pair and from malformed hex")
val r = pointcut_match_cache_acquire_v1(pointcut_match_cache_new_v1(),
    pointcut_selector_parse_v1("attr(logged)"), dir_a([]))
val hex = r.key.slice(9, r.key.len())
step("Valid hex round-trips to the same key; empty or non-hex input gives none")
expect(r.key.starts_with("xxh3-128:")).to_equal(true)
expect(pointcut_local_key_from_hex_v1(hex)).to_equal(r.key)
expect(pointcut_local_key_from_hex_v1("")).to_equal("")
expect(pointcut_local_key_from_hex_v1("not-hex")).to_equal("")
```

</details>

### .rr schema v2 forward reads

#### emits directory-membership and match reads keyed by facts and match digests

- Emit forward reads for attr(logged) over directory a
- One membership read of the facts and one match read, both complete
   - Exec capture: after_step
   - Evidence: execution result verified by 7 expected checks
   - Expected: rs.len() equals `2)  # oracle: membership read + match read`
   - Expected: rs[0].producer.kind equals `aop.directory_facts`
   - Expected: rs[0].consumer.kind equals `aop.match`
   - Expected: rs[0].facet equals `membership:join-points`
   - Expected: "sha256:" + rs[0].witness_digest equals `f.negative_root`
   - Expected: rs[1].consumer.kind equals `aop.weave`
   - Expected: rs[0].completeness equals `SemanticCoverageV1.Complete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A03
step("Emit forward reads for attr(logged) over directory a")
val f = dir_a([])
val sel = pointcut_selector_parse_v1("attr(logged)")
val rs = aspect_match_forward_reads_v1(sel, f, pointcut_match_shard_compute_v1(sel, f), f.facts_key)
step("One membership read of the facts and one match read, both complete")
expect(rs.len()).to_equal(2)  # oracle: membership read + match read
expect(rs[0].producer.kind).to_equal("aop.directory_facts")
expect(rs[0].consumer.kind).to_equal("aop.match")
expect(rs[0].facet).to_equal("membership:join-points")
expect("sha256:" + rs[0].witness_digest).to_equal(f.negative_root)
expect(rs[1].consumer.kind).to_equal("aop.weave")
expect(rs[0].completeness).to_equal(SemanticCoverageV1.Complete)
```

</details>

#### an incomplete directory emits conservative reads and a fast-keyed one emits none

- Emit reads for an incomplete directory and for facts keyed with xxh3-128
- Incomplete facts are read conservatively; a non-SHA-256 digest emits no read at all
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: conservative.len() equals `2)  # oracle: membership read + match read`
   - Expected: conservative[1].completeness equals `SemanticCoverageV1.Conservative`
   - Expected: none equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A04
step("Emit reads for an incomplete directory and for facts keyed with xxh3-128")
val sel = pointcut_selector_parse_v1("attr(logged)")
val inc = incomplete_dir("p")
val conservative = aspect_match_forward_reads_v1(sel, inc,
    pointcut_match_shard_compute_v1(sel, inc), inc.facts_key)
val fast = fast_keyed_dir_a()
val none = aspect_match_forward_reads_v1(sel, fast,
    pointcut_match_shard_compute_v1(sel, fast), fast.facts_key)
step("Incomplete facts are read conservatively; a non-SHA-256 digest emits no read at all")
expect(conservative.len()).to_equal(2)  # oracle: membership read + match read
expect(conservative[1].completeness).to_equal(SemanticCoverageV1.Conservative)
expect(none).to_equal([])
```

</details>

### hash agility

#### tags every digest with its algorithm and rejects unknown/fast algorithms

- Classify the facts key and relabelled copies of its hex
- Only the SHA-256 tagged digest is a known identity
   - Exec capture: after_step
   - Evidence: execution result verified by 4 expected checks
   - Expected: aop_digest_known_v1(f.facts_key) is true
   - Expected: aop_digest_known_v1("xxh3-128:" + hex) is false
   - Expected: aop_digest_known_v1("md5:" + hex) is false
   - Expected: aop_digest_known_v1(hex) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A04
step("Classify the facts key and relabelled copies of its hex")
val f = dir_a([])
val hex = f.facts_key.slice(7, f.facts_key.len())
step("Only the SHA-256 tagged digest is a known identity")
expect(aop_digest_known_v1(f.facts_key)).to_equal(true)
expect(aop_digest_known_v1("xxh3-128:" + hex)).to_equal(false)
expect(aop_digest_known_v1("md5:" + hex)).to_equal(false)
expect(aop_digest_known_v1(hex)).to_equal(false)
```

</details>

#### an unknown-algorithm facts key is a miss and never admitted

- Acquire attr(logged) over facts whose key is relabelled xxh3-128
- The acquire is not cacheable and nothing is admitted
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: r1.cacheable is false
   - Expected: r1.cache.shards.len() equals `0)  # oracle: nothing may be admitted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-A04
step("Acquire attr(logged) over facts whose key is relabelled xxh3-128")
val r1 = pointcut_match_cache_acquire_v1(pointcut_match_cache_new_v1(),
    pointcut_selector_parse_v1("attr(logged)"), fast_keyed_dir_a())
step("The acquire is not cacheable and nothing is admitted")
expect(r1.cacheable).to_equal(false)
expect(r1.cache.shards.len()).to_equal(0)  # oracle: nothing may be admitted
```

</details>

#### negotiates over one to three digests; unknown entries are absent

- Match digest tables of different sizes and algorithms
- A shared SHA-256 entry matches; empty, oversized or fast-only tables never do
   - Exec capture: after_step
   - Evidence: execution result verified by 7 expected checks
   - Expected: aop_digest_tables_match_v1([s], [bl, s]) is true
   - Expected: aop_digest_tables_match_v1([s], [other]) is false
   - Expected: aop_digest_tables_match_v1(["xxh3-128:" + s.slice(7, s.len())], [s]) is false
   - Expected: aop_digest_tables_match_v1([s, bl, s, s], [s]) is false
   - Expected: aop_digest_tables_match_v1([], [s]) is false
   - Expected: aop_digest_tables_match_v1([s], []) is false
   - Expected: aop_digest_tables_match_v1([s], [s, bl, s, s]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-SHARD-COV
step("Match digest tables of different sizes and algorithms")
val s = dir_a([]).facts_key
val other = dir_b().facts_key
val bl = "blake3:" + other.slice(7, other.len())
step("A shared SHA-256 entry matches; empty, oversized or fast-only tables never do")
expect(aop_digest_tables_match_v1([s], [bl, s])).to_equal(true)
expect(aop_digest_tables_match_v1([s], [other])).to_equal(false)
expect(aop_digest_tables_match_v1(["xxh3-128:" + s.slice(7, s.len())], [s])).to_equal(false)
expect(aop_digest_tables_match_v1([s, bl, s, s], [s])).to_equal(false)
expect(aop_digest_tables_match_v1([], [s])).to_equal(false)
expect(aop_digest_tables_match_v1([s], [])).to_equal(false)
expect(aop_digest_tables_match_v1([s], [s, bl, s, s])).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-AOP-SHARD-A01`
- `REQ-AOP-SHARD-A02`
- `REQ-AOP-SHARD-A03`
- `REQ-AOP-SHARD-A04`
- `REQ-AOP-SHARD-COV`
- `REQ-AOP-SHARD-A01..A04`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2d8158cbb6ed0e855a3e86087fb72835f65bb534f3b940d27b310bc3da23dd53`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2d8158cbb6ed0e855a3e86087fb72835f65bb534f3b940d27b310bc3da23dd53`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2d8158cbb6ed0e855a3e86087fb72835f65bb534f3b940d27b310bc3da23dd53`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: 01_unit/compiler/aop/aspect_match_shard_v1_spec.spl
mirror: doc/06_spec/01_unit/compiler/aop/aspect_match_shard_v1_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/aop/aspect_match_shard_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/aop/aspect_match_shard_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
