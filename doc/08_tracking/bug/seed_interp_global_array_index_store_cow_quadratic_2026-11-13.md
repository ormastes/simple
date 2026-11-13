# Seed interpreter: module-global array index store deep-copies per write (quadratic)

- **ID:** seed_interp_global_array_index_store_cow_quadratic_2026-11-13
- **Severity:** P2 (performance; correct results, super-linear time)
- **Status:** fixed (seed); the spec that exposed it still exceeds the 900 s cap — see "Remaining"
- **Component:** Rust seed tree-walk interpreter
  (`src/compiler_rust/compiler/src/interpreter/node_exec.rs`, index-assignment Case 1;
  `src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs`, `release_global_aliases`)
- **Exposed by:** `test/01_unit/compiler_core/interpreter/stmt_for_comprehension_no_silent_iteration_cap_spec.spl`
  (timed out at 900 s twice after PR #8969 fixed its import error)
- **Related:** `core_interpreter_hard_loop_iteration_caps_2026-08-28.md` (the spec's parent bug;
  its 2026-11-05 update already measured "~60-75 min per 1M-iteration fixture", so the spec
  never fit 900 s — the import error only hid that), `seed_global_array_push_cow_per_frame_2026-08-22.md`
  (same class, `g.push(x)` path, fixed earlier).

## Classification of the "hang"

Not a hang, and no unbounded loop. The spec runs the pure-Simple core interpreter
(`core_interpret`) on three fixtures that each iterate 1,000,002 times, while the spec itself
is tree-walked by the seed (`jit-bail:no-main-fn`). Every fixture terminates with the right
answer:

| probe (seed `run`, `fn main` wrapper, JIT'd) | result | wall | RSS |
|---|---|---|---|
| `for i in 0..1000002: acc = acc + 1` | 1000002, no error | 31.1 s | 6.8 GB |
| `for i in 0..=1000001: ...` | 1000002, no error | 37.0 s | 6.8 GB |
| `[i for i in 0..1000002]` + `xs[1000001]` | len 1000002, last 1000001 | 12.6 s | 2.7 GB |

Comprehension scaling 100k / 300k / 1M = 3.4 / 4.6 / 12.6 s: linear.

Under the spec host (tree-walk), the statement-for fixture was super-linear in the iteration
count: 10k 11.5 s, 20k 22.5 s, 30k 43.6 s, 50k 80.0 s (ms/iteration rising 1.0 -> 1.6) while
the seed's dispatch count stayed exactly linear (~2,134 dispatches per iteration,
`SIMPLE_INTERP_PROFILE=1`, 10k vs 30k). Linear work + super-linear time = a hidden O(n) per
step.

## Root cause

`val_alloc` in `src/compiler/10.frontend/core/interpreter/value.spl` is an arena allocator over
11 parallel module-global arrays; every int >= 256 allocates (`val_ints[idx] = n`). Minimal
reproductions (seed `517f20ae777`, sha256 prefix `55a6b4d18e17c117`):

- index store on a module global from a function — `fn setk(i, n): k[i] = n` over a 25k / 100k
  array: 4.5 s / 80.8 s (x4 n -> x18 time);
- same-file and cross-module `push` + `k[idx] = n`: 2.0 s / 30.1 s and 2.0 / 7.3 / 29.6 s (25k/50k/100k);
- `val_make_int(1000 + i)` loop: 10k 0.74 s, 25k 2.66 s, 50k 9.0 s, 100k 34.0 s, 150k 77.0 s;
- entry-script top-level `k.push(0)` loop: 25k 1.9 s, 100k 39.6 s.

`SIMPLE_PERF_COUNTERS=1 SIMPLE_PERF_COUNTERS_TRACE=1000` pinned both:

1. **Index store (`k[i] = v`) inside a function.** The global is owner-bound (it has a
   `global_binding`), so `is_module_global` is false and the store took the generic path:
   `env.get(name).cloned()` then `Arc::make_mut`. The owner store
   (`MODULE_GLOBALS_BY_OWNER`) and the flat `MODULE_GLOBALS` mirror both still pin the Arc,
   so every element store deep-copied the whole array (trace: one `index_store_cow` per store
   for `val_ints`, 4,001 of 5,000 at len >= 1000).
2. **Entry top-level `g.push(x)`.** `release_global_aliases` parked the owner store only when
   `CURRENT_EXEC_MODULE` was set, but `sync_flat_global` re-publishes into `"<entry>"` when it
   is not. The `"<entry>"` store kept pinning the Arc (`store_pins=["owned:<entry>::k"]`, rc=2)
   and every top-level push deep-copied: `ARR_MUT_COW_ELEMS_CLONED 12,497,500` for 5,000 pushes
   (= n^2/2).

## Fix

- `node_exec.rs` Case 1: for a non-local array global that the executing module owns under the
  same name (`owns_global_binding`), park the store copies with `release_global_aliases`
  (exactly the `g.push(x)` mechanism), mutate the now-unique Arc in place with
  `assign_index`, then `sync_flat_global` + `refresh_scope`. Any other binding (imported from
  another owner, aliased under another name) keeps the generic copy-and-publish path. A real
  user alias still copies (value semantics).
- `patterns.rs` `release_global_aliases`: resolve the owner with the same `"<entry>"` fallback as
  `sync_flat_global`.
- New counters `INDEX_STORE_GLOBAL_IN_PLACE`, `INDEX_STORE_COW_CLONES`,
  `INDEX_STORE_COW_ELEMS_CLONED` (+ `index_store_cow` trace site).

## Evidence (same host, fixed seed built from this branch)

| probe | before | after |
|---|---|---|
| `setk` index store, 100k | 80.8 s | 0.47 s |
| push + index store (same file), 100k | 30.1 s | 0.57 s |
| entry top-level push, 100k | 39.6 s | 0.12 s |
| `val_make_int` arena loop, 150k | 77.0 s | 5.0 s |
| spec fixture 1 shape (tree-walked), 50k | 80.0 s | 53.5 s |

After the fix the spec-shaped probe at 20k shows no remaining COW clone of any arena array
(only one-off promotions), and its time is linear: 20k 20.3 s, 50k 53.5 s, 100k 83.0 s.

Value semantics checked with an alias / nested-call / local-shadow / extend-past-end /
cross-module probe: byte-identical output before and after. Regression test:
`src/compiler_rust/compiler/tests/interpreter_global_array_index_store_in_place.rs`.

## Known remaining gap

An index store on a global bound under a different owner or name (imported/aliased binding)
still takes the generic copy-and-publish path and deep-copies per store. The new path also
publishes to both stores at the store itself rather than at call-out/return (earlier
visibility, same final state).

## Remaining (not fixed here — owner decision)

The spec still exceeds the 900 s runner cap: after the fix its cost is the linear constant of
running the core interpreter under the seed's tree-walker, ~0.8 ms per interpreted iteration
(~139 seed calls per iteration), and it needs 3,000,004 iterations (~40 min). The fixed-binary
run was killed at `SPEC wall=900.03s rc=124`. The spec's bound must not be lowered (it has to
cross the old 1,000,001 cap). Options for the owner: run the spec examples on the JIT
(`SIMPLE_JIT_SPEC_ENTRY=1` currently falls back: "module has 1 top-level statement(s) that the
JIT entry path would silently skip"), grant the spec a long-run budget, or move it to a
slow-lane tag.
