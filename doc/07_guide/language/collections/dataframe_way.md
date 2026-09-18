# The dataframe way: no accidental O(n²) collection code

**Audience:** people and LLM agents writing Simple.
**Status:** library, profiler, lint rules and `simple fix` auto-fix are implemented on the
`work/adaptive-collections-typed-query` branch (specs green 2026-09-18). Check each spec verdict
before relying on one.

LLM-generated code often gets collection work wrong in the same few ways. It
calls `.contains()` on an array inside a loop. It nests two loops to match rows
by key. It dedups with a growing `seen` list. It sorts everything to keep the
top 3. Each of these is quadratic, or a full sort, hidden inside code that looks
correct. Simple catches these patterns and names the fast replacement.

## 1. Use the typed frame API over `[Record]`

```simple
use std.common.frame.{key_set, index_by, distinct_by, group_by_key, count_by, semi_join, anti_join, top_k_by}

val active = semi_join(users, sessions, \u: u.id, \s: s.user_id)   # O(u + s), user order kept
val teams  = group_by_key(users, \u: u.team)                      # first-encounter order
val best   = top_k_by(users, 3, \u: u.score)                      # no full sort
```

A plain typed collection (`[User]`) *is* the dataframe. The schema is the
record type, and you never convert to `DataFrame`. `std.df.DataFrame` remains
for runtime-shaped data such as CSV with unknown columns.

Inside the compiler, loader and interpreter, write the **inline Dict form**
until the closure-ABI gate is green:

```simple
var ids: Dict<i64, bool> = {}
for s in sessions:
    ids[s.user_id] = true
for u in users:
    if ids.contains_key(u.id):        # contains_key before d[k]; never .set()/.get()
        ...
```

## 2. The lint tells you when to switch

| Code | You wrote | Switch to | Auto-fix |
|---|---|---|---|
| COLL002 | `arr.contains(x)` in a loop | `key_set` / local `Dict<T,bool>` | yes, when the preconditions hold |
| COLL015 | nested loops matching `a.k == b.k` | `semi_join` / `index_by` | hint |
| COLL016 | `.find`/`.filter` on the outer loop key | `index_by` / `group_by_key` | hint |
| COLL020 | growing `seen` + `.contains` + `.push` | `distinct_by` / `unique` | yes, for guard + push bodies |
| COLL021 | scan a `keys` array for a group slot | `group_by_key` | hint |
| COLL022 | sort then `take(k)` | `top_k_by` | hint |

```bash
bin/simple lint path/to/file.spl         # one file per run
bin/simple fix path/to/file.spl         # applies only Certain fixes (COLL002, COLL020)
bin/simple lint --fix path/to/file.spl  # same, once the seed with 1f570918de4 is deployed
```

An auto-fix is applied only when its textual preconditions are proven. For
example, the receiver has to be an array declared with `[T]`, not `text`, and it
must not be mutated in the loop. Otherwise you get the message and the snippet
to paste. Rules and preconditions:
`doc/05_design/compiler/collection_planner/adaptive_collections_typed_query_design.md` §10.3.

## 3. Profile before guessing

```simple
use std.common.collection_profile.*
var p = coll_profiler_new()
val s = coll_site(p, "resolver.symbols")
# on each lookup: coll_on_lookup(p, s, hit, scanned, len)
for line in coll_advice(p): print line   # "recommend key_set/index_by ... dataframe-able"
```

Advice is cost evidence with the counts attached. It never claims a change was
made.

## Not yet

`users[.age >= 18][.name, .score]` field-query syntax, `{a, b}` set literals,
automatic representation switching and SIMD/GPU execution come after RC1. See
the plan: `doc/03_plan/compiler/collection_planner/adaptive_collections_typed_query_rc1_plan_2026-09-18.md`.
