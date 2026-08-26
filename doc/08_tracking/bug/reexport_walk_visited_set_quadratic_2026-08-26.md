# Re-export walk's per-root visited set is O(V^2) in time and allocation

**Date:** 2026-08-26
**Area:** `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`,
`src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl`
**Status:** RESOLVED 2026-08-26 — fix landed as `808f5cc2dd6`, measured ~9.5x here with a decision-identical proof
**ID:** REXVISIT

## NOT a duplicate of REXMEMO (`reexport_root_memo_deleted_glob_superlinear_2026-08-21.md`)

That record fixed the **outer** memo — the across-calls cache on `HirLowering`
(`reexport_root_memo_index` / `_item`, keyed `"{physical facade index} {wanted}"`),
which stops `find_reexport_source` from re-walking for a (facade, wanted) pair it
has already answered. That fix is intact and verified present at origin
(`reexport_root_memo_index`: 6 refs, `reexport_chase_memo_hits`: 2 refs).

This record is the **inner** structure: the per-root cycle state used *within a
single* `find_reexport_source_walk`. REXMEMO's write-up states "no linear
`hir_reexport_parallel_find` scan", which is true of the path it replaced but
NOT of the walk, where that function survives at origin (1 ref in each of the two
files above). A memo hit costs O(1); a memo MISS still pays the quadratic walk,
and on a poisoned module every chase is a miss.

## Symptom

Stage-3 self-host `native-build` does not finish: 64/713 modules in
10,771,806 ms, projecting ~33 h. RSS ~200 MB per module against a ~15 MB live
heap.

## Attribution correction (this cost three sessions of misdirection)

`[build] hir N/713 ... dt=Xms <module>` is emitted at a module's file:START, so
its `dt` is the cost of the PRECEDING module. Every "worst module" in earlier
reports is off by one:

| earlier claim | real owner of that time | that module's REAL cost |
|---|---|---|
| `common.diagnostics.span` 845 s | `compiler.driver.driver_log_helpers` | span = **59 ms** |
| `hir.hir_lowering.module_surface` 817 s | `compiler.driver.driver_types` | trivial |
| `driver.driver_aot_output` 489 s | `compiler.driver.driver_compiler_type` | |

Independently confirmed: a standalone `compile --format=smf` of `span.spl`
reports `imports=0ms/1 ... dt=97ms` — it has no import cost at all.

## Where the time actually goes

Attributed from absolute `+Nms phase3:hir:file:start|done` markers (84 starts):

- 26 modules complete normally: **4,063 ms total** (~156 ms each)
- 58 modules are POISONED (`ambiguous explicit callable dependency` ->
  `[hir-poisoned]`, no `file:done`): **11,888,595 ms = 99.97%**

The poisoned cost is a flat ~355-870 s FLOOR per module, essentially independent
of the fatal count (15 fatals -> 33 s each; 201 fatals -> 4.3 s each). It is not
per-error work.

Profiled (`SIMPLE_HIR_PHASE_PROFILE=1`, s2-base `3326932c...`):

| module | total | imports | `register` EXCLUSIVE | excl share |
|---|---|---|---|---|
| `driver_public_api.spl` | 346717 ms | 346674 ms | **346022 ms** | **99.8%** |
| `driver.spl` | 140713 ms | 140604 ms | **138932 ms** | **98.7%** |
| `driver_core_types.spl` | 127 ms | 125 ms | 17 ms | 13% |

All framed children on the hot modules are trivial (callable_deps 95 ms,
explicit_dep 125 ms, scan 85 ms, ...). `driver_public_api`: 2078 registrations /
346 s = **166 ms per registration** of UNFRAMED work.

## Root cause

`register_imported_symbol_inner` calls `find_reexport_source` on the branch where
the imported module does not itself declare the name — the common case for
facade-heavy driver modules. That call has no timing frame, so its cost was
booked to the caller's exclusive column, which is why profiling never named it.

Inside, `find_reexport_source_walk`'s per-root visited set is three PARALLEL
ARRAYS:

    val visit_entry = hir_reexport_parallel_find(       # O(visited) linear scan,
        state.surface_indices, state.wanted_names,      # text compare per entry
        facade_index, wanted)
    ...
    state.surface_indices = state.surface_indices.push(facade_index)   # COW copy
    state.wanted_names    = state.wanted_names.push(wanted)            # COW copy
    state.depths          = state.depths.push(depth)                   # COW copy

Both halves are O(visited) per node visited, so one chase is O(V^2) in time AND
in transient allocation. The three `state.xs = state.xs.push(v)` lines are
exactly the copy-on-write alias form `.claude/rules/code-style.md` forbids: each
deep-copies the WHOLE array per push. That is the 200 MB/module churn.

Instance of the class tracked in `value_semantics_cow_alias_perf_class_2026-08-21.md`.

## Two theories this replaces (recorded so they are not rebuilt)

1. **`ModuleSurface` pass-by-value.** Real (6.4x on the copy itself) but worth
   only ~1 ms/module against 800 s. It looked decisive because the quoted
   "82.9 ms/call exclusive" was actually the INCLUSIVE column —
   `register_imported_symbol` pushed no timing frame at all.
2. **Index threading (`1f795b9f92`).** Measured **0.57x aggregate (slower)**,
   ~0.88x after normalising a 0.65 box-contention factor. Delivered nothing.

## Fix (REXVISIT)

Replace the three arrays with one dict `visited_depth: {text: i64}` keyed
`"{surface_index} {wanted}"`, mutated through its single owner. The
bail/re-walk/record decision is bit-for-bit identical: a node already visited at
an equal-or-shallower depth bails as before, a node reached more shallowly lowers
its recorded depth and is re-walked, an unseen node is recorded.
`hir_reexport_parallel_find` is deleted (no other caller). The three-array
alignment guard goes with the arrays — one field cannot disagree with itself.

## Evidence bar for closing this

A/B on two Stage-2 binaries built from the same tree, differing only in this
patch, under the same harness. **The 26 normally-completing modules are the
contention control** — the previous theory's raw 0.57x read as a 1.75x
regression until the untouched modules exposed the 0.65 load factor. No speedup
may be claimed without that normalisation.

The narrow two-file REXVISIT implementation was transplanted into the current
render/bootstrap lane on 2026-08-26. Both touched files complete the repository
optimizer source analysis. A no-stub shard cannot yet reach HIR: it stalls in
the earlier `source_closure` phase at 704/1047 and hits the bounded 900-second
watchdog. Therefore this record remains open and makes no measured speedup
claim; `native_build_parse_shard_post_closure_stall_2026-08-26.md` owns the
earlier blocker.

## Prevention

The defect is not "someone wrote a slow scan" — it is that a visited set was
built from parallel arrays grown by COW alias assignment, and no gate saw it.
`check-cow-alias-hotpath.shs` ratchets the alias form; it did not fire here
because the pushes are on a local `state` carrier, not on `self`. Widening that
gate to carrier-typed locals in HIR lowering is the durable fix.

## RESOLVED 2026-08-26 — measured A/B, ~9.5x, behaviour proven unchanged

The status line above ("A/B blocked before HIR by source-closure stall") is
superseded: the A/B was completed in an isolated replica (`lane-perf6`, all
writable paths rebased into the lane; no other lane touched). The source fix
itself landed independently as `808f5cc2dd6` "perf(hir): make reexport visited
lookup constant time" — identical in substance to the patch measured here
(`visited_depth: {text: i64}`, `hir_reexport_parallel_find` deleted). What was
missing was the evidence, which is recorded below.

### Method

Two Stage-2 binaries built from the SAME tree by the same script, differing only
in this patch — legA unpatched (sha256 `4c024630…`), legB patched (sha256
`3356e79f…`) — each driving the same `native-build` of
`src/app/cli/bootstrap_main.spl` under the same env. Both ran CONCURRENTLY on
the same loaded host, so shared contention biases the comparison AGAINST the
patch, not for it.

### Speed — matched module indices, not wall clock

The first 85 modules are processed in a verified-identical order in both legs,
so `[build] hir N/713 … +Nms` is directly comparable at equal N:

| hir index | legA (unpatched) | legB (patched) | ratio |
|---|---|---|---|
| 20 | 4,504,027 ms | 482,263 ms | 9.34x |
| 40 | 7,247,950 ms | 765,390 ms | 9.47x |
| 60 | 9,511,920 ms | 992,332 ms | 9.58x |
| 80 | 10,163,694 ms | 1,063,268 ms | 9.56x |

**The stability of the ratio is the contention control.** The previous theory's
0.57x reading was a load artifact; a load effect drifts, and this holds to
+/-0.12x across a 4x span of work. That is what distinguishes a real speedup
here from the two refuted ones.

### Correctness — decision-identical, proven not asserted

At hir index 85 both logs sit at the SAME line number (3270), with **57**
`ambiguous explicit callable dependency` errors and **59** `[hir-poisoned]`
markers each. Extracting every semantic diagnostic (ambiguity / poisoned /
unresolved-type) and diffing the sorted sets: **959 lines on each side,
byte-identical.**

Two things that look like regressions and are not, recorded so the next reader
does not re-raise them:

- legB exited `RC=1` with 7,924 ambiguity errors against legA's 57. That is
  progress, not divergence: legB reached module 261 while legA was still at 85.
  At equal index the counts match exactly.
- The `[hir-prof-reg]` `completed`/`skips` counters differ between legs. Those
  are the visited set's OWN bookkeeping, which necessarily changes shape when
  three parallel arrays become one dict. No semantic line differs.

### Scope — what this does NOT fix

legB still hit the ambiguity wall and exited at 261/713. **The quadratic chase
was the COST of poisoning, not its CAUSE.** Stage 3 now walks ~9.5x faster into
the same wall; the residual wildcard-import ambiguity (overlapping globs in
`mir_instruction_graph.spl`, a different mechanism from the item-degenerate
case) remains the actual Stage-3 blocker. Do not read this row as "Stage 3
unblocked".

### Prevention landed

`scripts/check/check-cow-alias-hotpath.shs` was widened (`acce8d3fd1`) — it had
been anchored on the literal `self.` AND required the field as a call ARGUMENT,
so this defect fell through both holes at once. Baseline 191 -> 943.

### Final end-to-end numbers (both legs ran to completion)

| | legA (unpatched) | legB (patched) | ratio |
|---|---|---|---|
| wall to exit | 25,190,210 ms (7.0 h) | 2,632,363 ms (43.9 min) | **9.57x** |
| final module | 261/713 | 261/713 | same |
| exit | RC=1 | RC=1 | same |

Both legs stop at **exactly module 261 with the same RC**, which is the
strongest available confirmation that the patch is decision-identical: it
changes how long the walk takes and nothing about where it ends. The 9.57x
end-to-end matches the 9.34-9.58x measured at intermediate indices, so the
speedup is uniform rather than concentrated in one phase.

It also isolates the real blocker beyond argument: the ambiguity wall at module
261 is INDEPENDENT of this defect and is what actually stops Stage 3.
