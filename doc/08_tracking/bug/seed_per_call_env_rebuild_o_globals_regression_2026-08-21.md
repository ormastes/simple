# Seed interpreter rebuilds the whole callee env per call (O(module globals))

## Status
PARTIALLY RESOLVED — 408fb57b109 landed the initial mitigation (misses down 6.5x, wall still far above target); superseded by e73a0bec647 (scope-chain CowEnv replaces per-call env clone). OPEN: confirm wall-clock now meets target on the original repro.


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

## 2026-11-07 — OPEN item answered (wall does NOT meet target); where the per-call cost sits now, measured

Host: Windows 11. Binaries built from `origin/release/1.0.0` tip
`4eb1de2ecbd` with the bootstrap profile (`opt-level = "z"`, same for every
arm): `simple-base.exe` = pure tip (17883136 B, sha256 `c0c47b2cdd6cd6ee…`);
`simple-timers.exe` = tip + round-15 profiler tooling + phase timers
(behaviour-identical with the env vars unset).

**Wall on the original repro:** `lint src/compiler/80.driver/driver_types.spl`
= 162 s on the release seed (`D:/dev/wt/seed/simple.exe`, 2026-11-06), 124 s
on `simple-base.exe`, against the 60 s budget of
`check-lint-cost-budget.shs` and the 5 s target above. Not met. (The
any-rules `check` child exits 1 on this host, so these exclude that lane;
same in every arm.)

**The scope chain works; the remaining cost is elsewhere.** Micro-benchmarks
(`SIMPLE_EXECUTION_MODE=interpret`, 20,000 iterations each, `simple-base.exe`):

| call shape | ns / iteration |
|---|---|
| loop body `acc = acc + i` | 6-9 |
| same-file `fn local_fn(x) = x + 1` | 35 (first loop 290) |
| same-file fn whose body calls builtin `math_min_i64(a, b)` | 13,707 |
| builtin `math_min_i64(i, 7)` called directly from `main` | 6,609 |
| imported `std.common.math.min_i64(i, 7)` (module-owned, no globals) | 14,337-15,543 |
| imported `compiler.core.parser.par_kind_get()` | 12,113-16,241 |
| imported `compiler.core.lexer_chars.is_ident_char("a")` | 100,990 |
| inline module-global array read `g_slot[0]` from `main` | 2,369 |
| same-file fn that reads one module-global slot | 7,413 |
| local `arr[0] = arr[0] + arr[1]` | 2,602-2,789 |

So a call is cheap (35 ns) until its body contains a *call* or touches a
*module global*: then it costs 7-16 us, and a builtin call alone is 6.6 us.
Per-owned-call phase timers (`SIMPLE_PERF_COUNTERS=1`, OWNED_* / BODY_*,
120,005 owned calls in the `min_i64`/`abs_i64`/`is_digit`/`is_alpha` bench):

| phase (ns per owned call) | |
|---|---|
| publish_and_repoint | 186 |
| captured_env_with_live_globals (scope attach) | 795 |
| capture_argument_places | 127 |
| bind_args_with_values_named | 409 |
| park_written_back_arguments + release_scope | 245 |
| **execute_function_body** | **15,757** |
| sync_owned_captured_globals | 375 |
| write_back_mutable_arguments | 1,001 |
| restore_parked_arguments / write_back_borrow_arguments | 39 / 42 |
| body prelude (coverage/mem/sampler frames, CONST_NAMES swap, owner swap) | 925 |
| mark_block_locals | 108 |
| body epilogue (return contract, unsigned coerce, async wrap) | 242 |

The call-path WRAPPER (everything this record's earlier fixes targeted) is
~3.2 us; the body of a one-statement function is 15.7 us, i.e. the cost is
in evaluating the statement — the `evaluate_call` priority ladder and the
extern dispatch for `math_min_i64`. Per-rung timers (EVALCALL_* /
EXTERN_*) are in the tree; their numbers follow in the next note.

Lint's lexer calls across modules several times per character
(`is_ident_char` -> `is_alpha`/`is_digit` -> `char_code`), so at 10-100 us
per such call the 82 KB file's 124 s is accounted for by call count times
this constant, not by any superlinear term.

### 2026-11-07 (later) — the ladder numbers, and the two rungs that stopped paying

`SIMPLE_PERF_COUNTERS=1` on the same bench (`simple-timers2.exe`, 100,009
identifier calls; `math_min_i64` is a Simple fn in `std.common.math`, so
EXTERN_CALLS=5 — the "builtin" above was never an extern):

| evaluate_call rung (ns per identifier call) | before | after |
|---|---|---|
| P1 extern check (EXTERN_FUNCTIONS + has_local_def + shadows) | 423 | **149** |
| P2 `eval_builtin` string match (miss) | 644 | 572 |
| P3 `eval_bdd_builtin` string match (miss) | 378 | — |
| P3.9 local callable | 101 | — |
| P4 overloads | 252 | — |
| P4.5 decorated sentinel (`format!` + env cascade) | 502 | **52** |
| P4.9 env shadow check | 242 | 267 |
| P5 flat exec (inclusive of the callee) | 16,564 | — |

Landed: P4.5 gated on `decorator_apply::any_decorated_fn_bound()` (set by
all three sentinel writers), and `local_callable_shadows` evaluated only on
the extern/builtin branches. ~0.7 us per call off a ~7 us fixed cost; the
end-to-end bench swung 6.6-13.3 us for the UNCHANGED binary between runs as
other lanes loaded the host, so the claim rests on the per-rung counters,
not on wall. Prevention:
`test/01_unit/interpreter/call_ladder_miss_path_prevention_spec.spl`.

What is left per call, in cost order, each a separate change: P2/P3 are
sequential string matches over every builtin arm (a miss walks them all —
a name-keyed pre-check must be derived from the arms, not hand-copied);
the body prelude (925 ns: two TLS `take`s, owner swap, per-param
`mark_local` String clones); `captured_env_with_live_globals` (795 ns: three
SipHash lookups keyed by the ~70-byte owner path); `write_back_mutable_arguments`
(1.0 us on calls with no mutable args). None of these is O(globals); the
per-call cost is now a sum of constant rungs, which is why the 60 s lint
budget on `driver_types.spl` is still missed (124 s).
