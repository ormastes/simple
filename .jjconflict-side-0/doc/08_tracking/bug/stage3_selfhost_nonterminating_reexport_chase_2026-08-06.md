# Stage 3 self-host was NON-TERMINATING (not crashing): unmemoized `find_reexport_source` re-walked a cyclic import graph to its depth cap

- **ID:** stage3_selfhost_nonterminating_reexport_chase_2026-08-06
- **Status:** FIXED (commit `548f2d3b1f6`, RXM1)
- **Severity:** high — blocked task #18 (genuine pure-Simple self-hosted binary)
- **Area:** compiler / HIR lowering (`src/compiler/20.hir/`)

## Symptom, and why it was misread

Stage 3 (`stage2-simple native-build ... src/app/cli/bootstrap_main.spl`)
produced a near-empty log, no binary, and disappeared. It looked exactly like
the SIGNAL-death of the previous blocker (`030ff43e330`), and was initially
chased as one.

It was not a crash at all. **The compiler never failed and never finished.**

Terminal facts, from a run launched under gdb (`ptrace_scope=1` blocks
`gdb -p` attach on this box, so launch under gdb rather than attaching):

- **No signal stop.** gdb reports SIGSEGV/SIGABRT with a backtrace; it reported
  neither. The process simply kept allocating.
- **`VmStk` pinned at 132 kB across 309 samples** — ordinary stack. This is NOT
  the stack-overflow class of `030ff43e330`. That fix is intact and unrelated.
- **`VmRSS` 96 MB -> 39.4 GB, `VmPeak` 44.2 GB, monotonic over 26 minutes**, still
  climbing when killed. Earlier sightings that read as "dies at 13.7 GB" were
  **not** an internal cap or an OOM — 13.7 GB was just where that particular
  run happened to be killed.
- **Progress frozen at `tasks_done=2/6`** (`phase=parse ... current=complete`)
  for the entire run.

`/proc/<pid>/status` sampling is the cheap discriminator here and needs no
ptrace: flat `VmStk` + climbing `VmRSS` rules out stack exhaustion immediately.

## Root cause

`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:1053`,
`find_reexport_source`.

Its `depth > 8` bail was the function's **only** terminator — precisely the
state GLB2 (2026-08-01) found the sibling walker
`register_glob_imported_symbols_depth` in and fixed there with a memo, but
never here. The import graph is cyclic (GLB2 measured 168 directed 2-cycles
over 3,026 `use x.*` edges), and this function has **three** recursive call
sites (the import hop, the package-sibling star hop, the alias hop), each
branching over the facade's entire import/export list. A miss therefore
re-walks an exponential number of paths to the cap, and nothing caches that.

Localized by poor-man's-profiler sampling: gdb `thread apply all bt` at 60s
intervals showed **exactly 9 nested `find_reexport_source` frames** — the depth
cap fully unrolled — in every mid-flight HIR-phase sample, called from
`register_imported_symbol`.

## Fix (RXM1)

Memoize **misses only**, keyed `"<facade key>\t<wanted item>"` -> the shallowest
depth at which the pair was proven absent, reusing GLB2's shallowest-wins rule:
a deeper arrival carries less budget and explores a strict subset, so a
recorded miss is sound for it, while a shallower arrival re-explores. Hits
already return immediately and unwind the stack, so only the exhaustive
not-found search is worth caching. The `depth > 8` bail is deliberately NOT
recorded — that is budget exhaustion, not proven absence.

The answer is a pure function of `(module_surfaces, facade, wanted, budget)` —
the function reads no per-file state — so the memo spans the whole build and is
keyed to the surface COUNT so it self-invalidates if that set grows.

## Evidence (peak RSS and chase counts are program properties; wall-clock only
## reflects who killed the run, so it is reported but not relied on)

| leg | wall | peak RSS | chase calls / memo hits | phase reached |
|---|---|---|---|---|
| RED (no memo) | 900s* | 23.3 GB | n/a | parse, `tasks_done=2/6` |
| SAB (memo read disabled, 1 line) | 400s* | 12.0 GB | 240,000+ / **0**, climbing | parse, `tasks_done=2/6` |
| GRN (fix) | 131s | 5.2 GB | n/a | hir, real diagnostic |
| VER (fix, independent cycle) | 127s | 5.2 GB | 20,000 / 16,203 | hir, real diagnostic |

`*` killed by the budget; did not finish. `VmStk` 132 kB in every leg.

**Sabotage check:** SAB changes exactly one line (the memo's early return) and
nothing else. The exact symptom returns — frozen at `tasks_done=2/6`, unbounded
RSS, zero diagnostics — with 240,000 chase calls at **0** memo hits and still
rising. With the memo, 16,203 of 36,203 queries (44.8%) are served from it and
the entire HIR phase completes within 20,000 calls.

## Scope — this does NOT complete Stage 3

No `stage3-simple` binary is produced in any leg. Stage 3 now gets **past this
wall**: it reaches the HIR phase and fails fast (127s, exit 1) with a real
diagnostic, `unresolved type: ByteOrder` in
`src/compiler/driver/watcher/watcher_client.spl` — the separate already-OPEN
blocker in
`t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`.

That ByteOrder error is **not** caused by this memo. A wrongly-memoized miss
would produce exactly that symptom, so it was checked directly rather than
argued: a level-gated trace (`SIMPLE_HIR_REEXPORT_TRACE_NAME=ByteOrder`)
recorded **zero** MEMO-SUPPRESSED events across a full run, and the bug
predates this change in `origin/main`.

## Refuted en route — do NOT re-chase this

`try_register_bootstrap_global_symbol` (`module_lowering.spl:896`) rescans all
804 module surfaces per unresolved name **with no negative memo**, so every
miss re-pays the full scan. It looks exactly like the bug and it is NOT the hot
loop. A work counter compiled into that very function fired **zero** times in
900s — fewer than 20,000 calls total — while `eprint` from the same binary was
demonstrably reaching the log (the `[hir-field-type]` probe lines appear in it).
Absence of counter output was confirmed to be about call count, not plumbing.

The two `[hir-field-type]` lines that were the last output before death carry
**no temporal information**: `declaration_lowering.spl:666` is hardcoded to two
struct/field pairs (`CompiledUnit.entry_point`, `BackendError.span`) that lower
early, with arbitrary work after. `actual == optional` there merely means those
fields' kind IS the `Optional` variant.

## Family closed

`grep -n "depth > [0-9]" src/compiler/20.hir/**/*.spl` finds exactly two
depth-capped recursions, and **both are now memoized**:
`module_lowering.spl:1038` (`find_reexport_source`, RXM1) and
`module_lowering.spl:1397` (`register_glob_imported_symbols_depth`, GLB2).
No unmemoized sibling remains in this layer.

## Level-gated diagnostics left in place

`SIMPLE_HIR_REEXPORT_STATS=1` — periodic `calls/memo_hits/memo` readout.
`SIMPLE_HIR_REEXPORT_TRACE_NAME=<Item>` — prints every MEMO-SUPPRESSED event for
one item, which is how to disprove (or prove) a suspected over-memoization.
Both default off.
