# Interpreter: the call-entry global publish walks the caller's WHOLE overlay, twice, on every call

- Status: RESOLVED (2026-09-13, PERF-9) — mechanism isolated by counting, then
  removed; pinned by counts in
  `test/05_perf/interp/call_entry_publish_scan_spec.spl`.
- Found: 2026-09-13, PERF-9, isolating the caller-frame-width term PERF-7
  measured but could not attribute.
- Component: seed tree-walk interpreter —
  `src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs`
  (`publish_and_repoint` -> `publish_live_bound_globals`) and
  `src/compiler_rust/compiler/src/value.rs`
  (`CowEnv::drop_published_globals`).
- Lane: interpreter (`SIMPLE_EXECUTION_MODE=interpreter`).
- Binaries: BASE `633b3aabe70c149b9400` (built from `2cb951036a4`,
  `CARGO_TARGET_DIR=/home/yoon/cargo-perf9`), CANDIDATE `f6e809bdd9290846e626`.

## The finding PERF-7 left open

PERF-7's component attribution measured a class-method call getting **~650 ns
slower for 20 extra locals in the CALLER** — `m5_wide_caller` (3,830 ns/iter)
against `m4_mod_method` (2,950 ns/iter), two fixtures whose loop, callee and
call site are byte-identical and which differ only by twenty `val`s in `main`.
The receipt recorded the term as "mechanism NOT isolated".

## The mechanism, counted

`publish_and_repoint(outer_env)` runs on every call out of a frame. It is three
steps, and **two of them walk the caller's entire overlay**:

- `publish_live_bound_globals(env)` iterated `env.overlay_entries()` and asked
  `is_local(name)` — two `String` hashes against two hash sets — for every
  entry, to discard almost all of them;
- `CowEnv::drop_published_globals()` iterated `self.overlay.keys()` with the
  same `is_local` filter.

Two counters (`PUBLISH_GLOBALS_SCANNED`, `PUBLISH_GLOBALS_NONLOCAL`,
`PUBLISH_GLOBALS_PUBLISHED`, added on this lane) settle it. `n = 2,000,000`,
`SIMPLE_PERF_COUNTERS=1`, BASE seed:

| fixture | CALLS | SCANNED | per call | NONLOCAL (whole run) | PUBLISHED |
|---|---:|---:|---:|---:|---:|
| `m4_mod_method` (3 caller locals) | 2,000,002 | 6,000,005 | **3** | 1 | 0 |
| `m5_wide_caller` (+20) | 2,000,002 | 46,000,026 | **23** | 1 | 0 |

The difference is exactly 20 entries per call — the caller's extra locals, one
for one — and **across both entire runs one entry survived the filter and none
was ever published**. Forty-six million string hashes to publish nothing. This
is the width term, and it is not specific to the wide fixture: every one of the
21,601 `src/lib/common` method call sites pays it in proportion to whatever
its caller happens to hold.

## The fix

`CowEnv` gains `nonlocal_overlay`, a lazily allocated SUPERSET of
`{ k in overlay : !is_local(k) }` — the only keys any of these walks can act
on. Maintained at the overlay's own mutation points (all private to `value.rs`)
and deliberately a superset, never an exact set: `entry()` hands out a raw
`Entry` that may or may not insert, and a stale extra name costs one failed
`overlay.get`, whereas a MISSING name would silently drop a global write.
Every consumer re-checks `overlay`, `is_local` and `is_refreshed_global`, so
over-approximation is unobservable.

Five call-path walks now iterate the superset instead of the overlay:
`publish_live_bound_globals`, `drop_published_globals`,
`refresh_live_bound_globals`, `sync_live_bound_globals` and
`sync_owned_captured_globals`.

After: `PUBLISH_GLOBALS_SCANNED` is **1 for the whole run** on both fixtures,
down from 6,000,005 and 46,000,026.

## Verification

- **The mutation-site audit is closed over the whole module.** Every writer of
  `overlay` / `local_bindings` / `block_local_bindings` is private to
  `value.rs`; `value_pointers.rs`, which is `include!`d into the same module and
  could therefore reach the private fields, was grepped and has **zero** such
  mutations.
- **The audit gate.** `SIMPLE_PERF_COUNTERS=1 SIMPLE_ENV_AUDIT=1` recomputes the
  exact set on every call-entry publish and aborts if the superset is missing a
  name. BOTH variables are required — the audit sits inside the counters'
  single `enabled()` load so the off-path cost of the whole block is one atomic
  read. Run under it with no abort, and verified to have actually reached the
  children by the `interp-perf-counters:` blocks in each log:
  `test/01_unit/interpreter/` (3 specs, 17/17, 3 counter blocks) and
  `test/05_perf/interp/` (8 specs, each of which spawns its own fixture
  children), plus PERF-7's 9-fixture corpus and this lane's 4 fixtures.
- `value_tests_nonlocal_overlay.rs`: thirteen mutation orderings (insert before
  and after `mark_local`, nested block shadow depth, remove/re-insert,
  `take_frame_owned`/`restore_frame_owned`, `entry()`, `get_mut` promotion,
  `refresh_globals`, `extend`, `clear`, `from_map`, `clone`), each asserting the
  audit oracle is empty, plus a direct equality check against the overlay walk
  the superset replaced.
- `test/05_perf/interp/call_entry_publish_scan_spec.spl` pins the narrow/wide
  SCANNED delta below one hundredth of an entry per call, and separately
  requires `PUBLISHED > 0` on a cross-module global round-trip, so a superset
  that silently went empty fails rather than passing with a wonderful scan
  count.

## Honest reading of the wall-clock half

Child USER+SYS CPU, interleaved A/B, medians of 6 (host load 4-20, 20 cores,
aarch64) — see the receipt for the final table. The width term shrinks as the
counts say it must, and a small constant is paid on narrow callers. The COUNTS
are the evidence; the times on this host are not
(`perf_wall_clock_ratio_unmeasurable_on_loaded_host_2026-09-13.md`).

## One deliberate behaviour change, stated rather than left implicit

`exec_function_with_self_return_values` now calls `local_env.mark_local("self")`
before binding the receiver, so the receiver never enters the frame's
publishable set (which would allocate a `String` and a hash table per call for
a name that can never be a module global). For `fn m(self)` methods
`execute_function_body` already marked that exact name local a moment later, so
nothing changes. For a `me fn` method with no explicit `self` parameter the
receiver was NOT previously marked local; the difference is unobservable
because every consumer of `is_local("self")` reaches the same answer either way
— `global_binding` returns `None` (no module global is named `self`),
`drop_published_globals` needs `scope.binding` which is likewise `None`, and
`steal_for_mutation` returns early instead of failing the same lookup one line
later (only the `STEAL_NO_BINDING` counter differs).

## Related

- `interpreter_per_call_cost_dominates_loop_bodies_2026-09-13.md` (PERF-6) —
  the per-call cost is the largest interpreter target by cost x frequency.
- PERF-7's attribution receipt, which measured this term and filed it
  unattributed.
