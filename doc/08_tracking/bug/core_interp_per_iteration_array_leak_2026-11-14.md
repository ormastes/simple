# Core interpreter leaks ~33 arrays per loop iteration on the seed JIT (15.2 GB spec peak)

- **Date:** 2026-11-14
- **Severity:** P3 (memory; verdicts unaffected)
- **Status:** mitigated (allocation sites removed). The root cause, that the seed JIT runtime never frees arrays, is still open; see "Remaining".
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
  outside this lane. Design options, measurements and a first slice:
  `doc/05_design/compiler/jit_memory/seed_jit_array_reclamation.md`. It also shows the
  18 frees are 9 per `core_interpret` call, independent of iteration count.
- **`val_alloc` still mints two empty arrays per fresh value slot.** These are the
  `val_struct_fields` / `val_struct_values` rows. Each one is ~128 B of data, because an
  empty `[]` literal reserves capacity, plus its header. Sharing one empty row is unsafe:
  `val_struct_add_field` pushes onto the row in place. A sparse struct side-table is the
  narrow fix. This is now most of the residual (~4.8 GB for the spec).
- **`stmt_get` / `expr_get` are still used on colder statement paths.** Each `stmt_get`
  costs four leaked arrays.
