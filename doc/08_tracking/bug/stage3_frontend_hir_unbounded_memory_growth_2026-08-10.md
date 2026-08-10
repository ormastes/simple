# Stage-3 self-host build: unbounded RSS growth in frontend/HIR lowering (~1 GB/min, no plateau)

- **ID:** stage3_frontend_hir_unbounded_memory_growth_2026-08-10
- **Status:** OPEN
- **Severity:** high — Stage-3 self-host cannot complete on a 64 GB host; the run
  is killed before codegen is ever reached.
- **Lane:** Stage-3 bootstrap (`SIMPLE_BOOTSTRAP=1`, **without**
  `SIMPLE_BOOTSTRAP_STAGE4=1`), x86_64-unknown-linux-gnu, cranelift.
- **Related (distinct):** `bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md`
  (STAGE4 lane, ~160 MB/file parse retention). This bug is the **flat-bootstrap
  (Stage-3) lane**, which takes a *different* code path — see "Why the existing
  guard is green" below.

## Symptom

A Stage-3 bootstrap run died at **~60 minutes with exit 143** and produced **no
verdict line**.

RSS climbed **essentially linearly with no plateau**:

| elapsed | RSS |
|---|---|
| 30 min | 26.5 GB |
| 39 min | 31.9 GB |
| 59 min | 52.5 GB |

≈ **1 GB/min, sustained, no flattening**.

All of the growth was inside **frontend / HIR lowering**. The native cache
**never received a single entry**, so codegen was never reached — the process
died in phase 2/3.

## READ THIS FIRST: exit 143 here is `earlyoom`, not a build failure

This has already misled multiple work streams. The host runs:

```
/usr/bin/earlyoom -r 3600 --prefer '^(simple|rustc|cc1|...)' --avoid '^(claude|codex|...)'
```

Verified live on this host (`pgrep -a earlyoom` shows exactly that command
line), with a hard journal receipt of the mechanism firing on a `simple`
process:

```
Aug 10 05:10:27 dl earlyoom[1479]: mem avail: 12849 of 128683 MiB ( 9.99%), swap free: 0 of 0 MiB
Aug 10 05:10:27 dl earlyoom[1479]: low memory! at or below SIGTERM limits: mem 10.00%, swap 10.00%
Aug 10 05:10:27 dl earlyoom[1479]: sending SIGTERM to process 3614902 uid 1000 "simple": badness 1075, VmRSS 20973 MiB
Aug 10 05:10:32 dl earlyoom[1479]: process exited after 5.1 seconds
```

Note the trigger is **10% of host RAM free**, not an absolute ceiling — a
`simple` process is killed well below the host's 128 GB whenever other work is
resident. `earlyoom` **preferentially SIGTERMs `simple` processes**. So the failure
presents as:

- exit status **143** (128 + SIGTERM), and
- **no verdict line / no compiler diagnostic of any kind**.

That signature reads exactly like "the build failed" or "the harness timed out".
It is neither. **Exit 143 + no verdict line = the process was killed from
outside.** Before attributing a Stage-3 death to a compiler defect, check
`dmesg`/`journalctl` for the earlyoom kill line and check the RSS trace. Two
previously-documented Stage-3 blockers were *ruled out* in this run precisely
because no diagnostic was emitted at all:

- `ByteOrder` unresolved type at `cache_validator.spl:38` — **did not fire**.
- `Effect` facade collision (6 co-compiled declarations, incl. a struct-vs-enum
  split at `src/compiler/20.hir/hir_types.spl:959`) — **did not fire**.

## Thread count does NOT affect the slope

A **2-thread** replay reached **7.7 GB at 7 min** — the **same ~1 GB/min**
slope. The growth is therefore **not thread-scaled**: it is not per-worker
arena duplication, not a thread-local cache, and it will not be tuned away with
`--threads`. It is a single, shared, monotonically-growing structure on the
per-module lowering path.

## Constraints on any hypothesis

Any proposed mechanism must satisfy all of:

1. **Linear in wall time, no plateau** across a ≥60 min window.
2. **Invariant in thread count** (1 GB/min at both 2 threads and the full run).
3. **Confined to frontend/HIR lowering** (native cache never populated).
4. Absent (or far weaker) in the **STAGE4** lane, which has its own separate,
   already-filed and separately-guarded blowup.

## Leading suspect (NOT yet established — see verdict)

`src/compiler/20.hir/hir_lowering/_Items/lowering_helpers.spl:30-107` holds
seven module-level **global accumulator arrays** written through a
**value-semantics functional push**:

- `lowering_helpers.spl:95` — `_bootstrap_hir_functions = _bootstrap_hir_functions.push(fn_)`
- `lowering_helpers.spl:59-65` — the same shape for the seven
  `_bootstrap_hir_module_*` arrays (arrays **of arrays**).

Simple arrays are **value types** and the bootstrap runtime is **no-GC**, so
`arr = arr.push(x)` allocates a full copy of `arr` and **never frees the old
one**. Lowering *F* functions in a module therefore retains ≈ *F²/2* copied
element sets, and `lower_parser_module_unstub`
(`_Items/module_lowering.spl:1841-1844`) then **re-pushes the whole set a second
time** into `flat_functions` — another O(F²).

Call sites, both gated on the **flat-bootstrap** predicate
(`bootstrap_mode and SIMPLE_BOOTSTRAP_STAGE4 != 1`), i.e. exactly the Stage-3
lane and **not** the STAGE4 lane:

- `_Items/module_lowering.spl:2099` — `bootstrap_hir_functions_add(hir_fn)`, per function.
- `_Items/module_lowering.spl:1854` — `bootstrap_hir_modules_add(...)`, per module.
- `_Items/module_lowering.spl:1811` — `bootstrap_hir_modules_reset()`, which under
  `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1` runs **only for the entry module**, so the
  seven module-level arrays accumulate **every module of the whole closure**.

This fits constraints 1-4: it is a process-global single structure (thread
invariant), it lives on the per-module HIR lowering path (frontend/HIR), and it
is gated OFF in the STAGE4 lane.

## Why the existing guard is green

`scripts/check/check-stage4-selfhost-parse-memory-multifile.shs:237` sets
`SIMPLE_BOOTSTRAP_STAGE4=1`. That makes `bootstrap_flat_mode` **false**, so the
guard **never executes the `_bootstrap_hir_*` accumulators at all**. The Stage-3
lane has **no memory guard of its own**. That gap is itself a defect: it is why
this class could grow to 52 GB with every gate green.

## Repro without a 60-minute build

`build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple` (the binary that
compiles Stage-3) driving a small synthetic N-file `--entry-closure` chain with
`SIMPLE_BOOTSTRAP=1` and **`SIMPLE_BOOTSTRAP_STAGE4` unset**, sweeping
functions-per-file. The O(F²) hypothesis predicts peak RSS **quadratic in
functions-per-file** at fixed file count; a retention-only mechanism predicts
linear. Probe harness kept out of tree at
`<scratchpad>/probe.sh` (mirrors the STAGE4 guard's generator, minus
`SIMPLE_BOOTSTRAP_STAGE4=1`).

## Verdict

**Root cause NOT established.** A concrete, well-fitting suspect is named above
with file:line, but the discriminating measurement has not been completed.

**Next measurement (cheap, bounded — do this before anything else):** the
functions-per-file sweep in "Repro" above at fixed file count (e.g. 20 files ×
{20, 80} funcs/file, 1 thread, `ulimit -v`, `timeout`). A **~16x** RSS jump for a
4x funcs/file increase confirms the O(F²) push-clone; a **~4x** jump refutes it
and points instead at plain per-module retention (i.e. the flat-AST arenas
`decl_*`/`stmt_*`/`expr_*` in `src/compiler/10.frontend/core/_Ast/`, which the
streaming driver only clears via a **single** `ast_reset()` **after all modules
are lowered** — `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:229`).

## Follow-on work regardless of verdict

1. Add a Stage-3-lane (flat-bootstrap) analogue of
   `check-stage4-selfhost-parse-memory-multifile.shs`. The lane is currently
   unguarded for memory.
2. Replace the functional `arr = arr.push(x)` accumulator idiom in
   `lowering_helpers.spl` with an in-place append, or drop the global arrays in
   favour of reading the already-retained `HirModule`s.
3. Never read exit 143 from a `simple` process as a build failure without first
   excluding earlyoom.
