# Core interpreter leaks ~33 arrays per loop iteration on the seed JIT (15.2 GB spec peak)

- **Date:** 2026-11-14
- **Severity:** P3 (memory; verdicts unaffected)
- **Status:** mitigated (allocation sites removed; `val_alloc` rows and cold `stmt_get` paths closed in the follow-up below). The root cause, that the seed JIT runtime never frees arrays, is still open; see "Remaining".
- **Lane:** Opus (Fable unavailable)
- **Exposed by:** `test/01_unit/compiler_core/interpreter/stmt_for_comprehension_no_silent_iteration_cap_spec.spl`
  (`# @jit_spec_entry`). It peaked at 15.2 GB, close to the 16 GB cap. That is the residual
  recorded in `seed_jit_spec_entry_demoted_by_entry_reparse_2026-11-14.md`.

## Diagnosis (corrects the earlier note)

The earlier note blamed the core interpreter's value arena: it said the arena was "not
reclaimed between `core_interpret` calls". That is only a symptom. Nothing in a JIT'd
program is reclaimed at any point:

- **The seed JIT runtime has no array reclamation.** JIT'd Simple code never frees an
  array object. Overwriting `xs = []`, a `val row = owner[i]` copy going out of scope, and
  a struct temporary dying all leave the array live. `rt_array_free` is emitted only for one
  narrow struct-field-overwrite case (`mir/lower/lowering_stmt.rs`).
- **Measured on the runtime heap counters.** After two 10k-iteration `core_interpret` runs:
  `allocs=700504 frees=18`.

Memory therefore grows with the number of arrays allocated, across the whole process, so
the "between examples" growth is the per-iteration growth summed. The core interpreter
allocated arrays on its hottest paths. These are the per-iteration counts for
`for i in 0..N: acc = acc + 1`, attributed with `rt_heap_live_count_by_kind(2)` micro-probes:

| site | arrays / call |
|---|---|
| `env_push_scope` reusing a slot: `scope_hm_keys[d] = []` (×3 rows) | 3 |
| `env_define`: `val r_keys = scope_hm_keys[top]` row copies | 3 |
| `env_lookup`: 4 row copies per scope searched | 4 per scope |
| `env_assign`: 3 row copies per scope searched | 3 per scope |
| `eval_stmt`: `stmt_get(sid).tag` (CoreStmt = body copy + 3 empty lists) | 4 |
| `eval_stmt_assign` / `eval_stmt_compound_assign`: `stmt_get(sid)` | 4 |
| `val_alloc` (fresh slot): `val_struct_fields.push([])` + `val_struct_values.push([])` | 2 per non-cached value |

Total: 33 arrays and about 5 KB per iteration. A 1M-iteration example is therefore about
5-6.8 GB, and the spec's three examples add up to 15.2 GB.

## Fix

The fix is in pure Simple, in the core interpreter (`src/compiler/10.frontend/core/interpreter/`):

- **`env.spl`**
  - `env_push_scope` clears a reused slot's rows in place with `.clear()` through the
    owner, instead of assigning `= []`.
  - `env_define`, `env_assign`, `env_lookup` and `env_get_local` read through the owner
    (`scope_hm_keys[si][idx]`) instead of binding row copies.
- **`eval_stmts.spl`**
  - `eval_stmt` reads the tag with `stmt_get_tag(sid)`.
  - `eval_stmt_expr`, `eval_stmt_assign` and `eval_stmt_compound_assign` use
    `stmt_get_expr`, `stmt_get_type` and `stmt_get_body` instead of building a CoreStmt.

Nested `g[i].clear()` was checked on both lanes (JIT and `SIMPLE_EXECUTION_MODE=interpret`):
it empties only that row, and later pushes land in it.

## Evidence (aarch64 DGX Spark, serial, MemoryMax=16G)

The change is `.spl`-only, so before and after use the **same binary**: the worktree seed
`target/release/simple`, sha256 `a6456302e14307e0…`. The stdlib/compiler source is read on
every run.

| run | before | after |
|---|---|---|
| `SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_SPEC_ENTRY=1 SIMPLE_JIT_STRICT_ALL=1 run stmt_for_comprehension…_spec.spl` | 4/4 pass, WALL 182.7 s, **RSS 15,215,584 KB** | 4/4 pass, WALL 35.0 s, **RSS 4,832,384 KB** |
| stats repro: 2× `core_interpret` of a 10k-iteration `for` | 33 arrays and ~5.0 KB per iteration | 5 arrays and ~0.95 KB per iteration |
| list-comprehension repro (10k) | — | 2 arrays per iteration (val_alloc) |

Regression spec: `test/01_unit/compiler_core/interpreter/env_scope_ops_no_array_leak_spec.spl`
(`@jit_spec_entry`). Before the fix: 2 passed, 3 failed (the control and the slot-reuse
semantics pass; the scope-ops, fast-local and loop-bound examples fail). After: 5/5.

## Remaining (filed, not fixed here)

- **Root cause: the seed JIT never frees arrays.** Every array a JIT'd program allocates
  stays live until exit, so any long-running JIT'd Simple program grows without bound.
  Fixing it needs ownership- or refcount-driven drops in MIR lowering, which is a redesign
  outside this lane.
- **`expr_get` is still used on statement paths** (`eval_stmt_expr`, `eval_stmt_assign`,
  `eval_stmt_compound_assign`, the range check in `eval_stmt_for`). Each call builds a
  CoreExpr with two array fields. Not converted here.
- **`stmt_get_body` / `elif_get_body` build a body copy per execution** (one array per
  `for` / `while` / `if` / `match` / block statement). Removing it needs an indexed body
  reader instead of a `[i64]` return.
- **`resolve.spl` still calls `stmt_get`.** It runs once per function, not per iteration,
  and reads `else_body`, which `stmt_get` always fills with `[]`, so it is not a mechanical
  swap.

## Follow-up 2026-11-14: sparse struct rows and cold statement paths

Two of the items filed above are fixed (pure Simple, same directory).

- **`value.spl`: struct rows are sparse.** A value slot holds a row id in `val_struct_rows`
  (-1 = none) into a side-table (`struct_row_fields` / `struct_row_values`) with a free
  list. A row is minted only by `val_make_struct`, or by the first
  `val_struct_upsert_field` on a slot that has none. `val_alloc` and `val_free` allocate
  no array. A released row keeps its stale contents and is overwritten by assignment on
  reuse; it is not cleared in place, because on the seed JIT the row can alias the array
  the caller passed to `val_make_struct` (true before this change as well).
- **`value.spl`: struct field reads go through the owner.** `val_struct_get_field`,
  `val_struct_get_field_idx`, `val_struct_check_field_idx` and `val_struct_find_field_idx`
  used to bind `val fields = rows[vid]`, a leaked row copy per field read.
- **`eval_stmts.spl`, `eval_decls.spl`: no `stmt_get` left.** val/var/lazy decl, return,
  if, while, for, static-for, comptime, match, block, break/continue, defer/errdefer,
  receive, bind, labeled loop and the computation-expression bind now use
  `stmt_get_tag` / `_expr` / `_name` / `_type` / `_span` / `_body`.

One behaviour note: a struct reader given an out-of-range value id now answers "no fields"
instead of indexing the per-slot rows out of range.

### Evidence (same host, serial, MemoryMax=16G)

Before and after use the same seed binary, sha256 `a6456302e14307e0…`; before is a
worktree pinned at `76f3263aa71`. The after column shows two runs.

| run | before | after |
|---|---|---|
| JIT spec-entry `run stmt_for_comprehension…_spec.spl` | 4/4, WALL 24.8 s, RSS 4,865,328 KB | 4/4, WALL 13.9 s / 17.2 s, RSS 3,059,988 / 3,046,864 KB |
| `simple test stmt_for_comprehension…_spec.spl` | WALL 30.5 s, RSS 4,806,156 KB | WALL 17.7 s / 14.1 s, RSS 2,985,780 / 3,035,536 KB |
| arrays per 1,000 fresh int + float + text slots | 6,000 | 0 |
| arrays per 1,000 alloc/free cycles on one recycled slot | 4,000 | 0 |
| arrays per iteration, `val` decl + `while` + `if` loop body | 60 | 4 |

Regression spec: `test/01_unit/compiler_core/interpreter/val_struct_rows_sparse_spec.spl`
(`@jit_spec_entry`): 9/13 before (the two slot examples and the two per-iteration bounds
fail), 13/13 after. Its struct-semantics examples (create, field write, upsert, value copy,
nested struct, struct in array, freed-row reuse) pass on both sides and on
`SIMPLE_EXECUTION_MODE=interpret`. All 27 existing specs in
`test/01_unit/compiler_core/interpreter/` report identical executed/passed/failed counts
before and after, including the four that are red on base.
