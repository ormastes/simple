# Seed interpreter rebuilds the whole callee env per call (O(module globals))

Status: PARTIALLY FIXED (2026-08-21) — misses down 6.5x, wall still far above target.
Area: Rust seed interpreter (`src/compiler_rust/compiler/src/interpreter_call/**`, `interpreter_state.rs`)
Blocks: stage1 `native-build` of `src/app/cli/bootstrap_main.spl` (phase2 parse 20-50 s/file, 7200 s worker timeout expires)

## Symptom

`bin/release/x86_64-unknown-linux-gnu/simple lint src/compiler/80.driver/driver_types.spl`
takes 207 s (measured 2026-08-21 09:20, shared box). Interpreted parsing of a
13 KB driver file takes 52 s, a 23 KB file 128 s. Sampled stack (investigator 2,
`scratchpad/fp/gdb_lint1.log:322-348`) sits in
`hashbrown::HashMap::insert` <- `arg_binding::bind_args_with_values` <-
`function_exec::exec_function_with_values_and_writeback_inner` <- `evaluate_call`.

## Not a regression from one commit

The per-call env rebuild predates today's seed commits; `git log --since=2026-08-18 --
src/compiler_rust/compiler/src/interpreter_call` shows the env-cache was ADDED
2026-08-18 (`7dc9d1f962f`) and extended today. Both the 05:10 seed and today's
build show the same cost, so this is an absolute cost problem (very likely the
unlocated superlinear term in `.claude/rules/commands.md`), not a bisectable
rewind.

## Mechanism

`captured_env_with_live_globals` caches a per-owner call-env TEMPLATE, keyed by
`(owner, captured-env template key)` and stamped with a thread-local
module-globals GENERATION. Every `GenTrackedCell::borrow_mut()` on any
module-global store bumps that generation, which drops EVERY template. The
interpreter write-back path takes such a write borrow on essentially every call
that touched a global, so the cache thrashed: measured `hits=1134558
misses=165442` in one lint of `driver_types.spl` — 165k full rebuilds, each
cloning the owner module env and re-resolving every imported binding.

## Fix applied (this change)

Dirty-name patching instead of cache-wide invalidation:

- `interpreter_state.rs`: a thread-local recorded-write log
  (`record_global_write` / `for_each_global_write_since` / `global_write_seq`)
  plus `GenTrackedCell::borrow_mut_recorded()`, which does NOT bump the
  generation. Unrecorded `borrow_mut()` still bumps, so an unrecorded mutation
  can never be observed stale. The log is capped (64k) and falls back to a bump
  when it wraps.
- `function_exec.rs`: the template cache stores `(generation, seq, env,
  by_source)`; a hit whose `seq` lags replays only the recorded writes into the
  template (`refresh_globals`, i.e. the same "refreshed global" marking
  `refresh_bound_global` uses, so nothing is written back twice).
  `publish_live_bound_globals` and `sync_owned_captured_globals` now record
  their writes instead of bumping.
- `patterns.rs`: the five `MODULE_GLOBALS` write-back sites route through a new
  `sync_flat_global`, which records the write and keeps `MODULE_GLOBALS_BY_OWNER`
  in step (needed so a later rebuild cannot resurrect the pre-write value).
- `arg_binding.rs` (landed by the bootstrap agent, kept here): `bind_args*` no
  longer builds a `HashSet` of every value-type class name per call; the copy is
  a post-pass with a by-name lookup. The array recursion added with it was
  narrowed to arrays containing VALUE-type objects, so arrays of reference-class
  objects keep their pre-2026-08-21 aliasing.

## Measurements (`lint src/compiler/80.driver/driver_types.spl`)

| build | env-cache misses | wall |
|---|---|---|
| 05:10 seed (`bin/release/x86_64-unknown-linux-gnu/simple`) | — | 207.6 s |
| + arg_binding + template-key cache | 165442 | 193.4 s |
| + dirty-name patching (publish + patterns) | 160562 | 170.5 s |
| + `sync_owned_captured_globals` recorded | **24777** | 130.4 s |

Wall times on this box are unreliable to about 2x (20-30 concurrent `simple`
processes; the same binary measured 130 s and 235 s an hour apart). The
miss count is the load-independent signal.

## Still open

- 130-235 s is still far above the 5 s target, with `hits=1.28M` now dominating:
  the remaining cost is the per-hit `Env::clone` (overlay + bindings) and the
  interpreter's own per-node work, not template rebuilds. Next structural step
  is a scope-CHAIN env (parent pointer, no per-call map at all) so a call is
  O(args); the template cache is a halfway house.
- Folding replayed patches back into the shared base every 64 hits was tried and
  made it WORSE (130 s -> 246 s): the O(globals) fold outweighs the overlay
  clone it saves. Reverted; do not retry without a cheaper compaction.
- Budget guard: `scripts/check/check-lint-cost-budget.shs` already pins this
  exact file (`COMPILER_FIXTURE_DEFAULT=src/compiler/80.driver/driver_types.spl`,
  budget 60 s) and is RED today. No new row was added; the existing row is the
  guard for this defect.
