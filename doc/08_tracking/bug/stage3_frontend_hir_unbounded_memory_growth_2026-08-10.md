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

## MEASURED 2026-08-10: the O(F²) suspect below is **REFUTED**

The discriminating sweep called for in "Next measurement" was run. **It did not
reproduce the growth at all**, and it refutes the leading suspect.

Harness: `build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple native-build
--entry-closure --threads 1`, `SIMPLE_BOOTSTRAP=1` with
**`SIMPLE_BOOTSTRAP_STAGE4` unset** (so `bootstrap_flat_mode` is TRUE and the
`_bootstrap_hir_*` accumulators DO execute), synthetic `mod0..modN` import chain.
Peak RSS from `/usr/bin/time -f %M`.

**Sweep A — functions per file, 20 files:**

| funcs/file | secs | peak RSS |
|---|---|---|
| 20 | 10 | 157.3 MB |
| 40 | 15 | 158.1 MB |
| 80 | 94 | 158.8 MB |

**Sweep B — file count, 10 funcs/file:**

| files | secs | peak RSS |
|---|---|---|
| 20 | 9 | 157.2 MB |
| 60 | 14 | 158.0 MB |
| 120 | 20 | 158.5 MB |

**RSS is FLAT — within 1% — across a 4x span of functions-per-file and a 6x span
of file count.** The O(F²) push-clone hypothesis predicted ~16x on Sweep A; even
plain linear retention predicted ~4x and ~6x. Both are refuted. Note Sweep A's
*time* is superlinear (10s → 94s) while memory is not — so the accumulators may
well be a real **compile-time** cost, but they are **not** the memory mechanism.

### Trap: the first version of this sweep was VACUOUS

The generator copied from `check-stage4-selfhost-parse-memory-multifile.shs`
makes each module export exactly ONE function and `main` call only that one. Under
`--entry-closure` the rest are dead-code-eliminated and never lowered:
`out.bin` was **byte-identical at 22832 bytes** for 20, 40 and 80 funcs/file, i.e.
4x the source produced 0% more output. The tables above are from the corrected
generator, where `f_j` calls `f_(j-1)` and `f_0` calls the previous module's last
function, so every generated function is live (out.bin then does grow, and Sweep
A's time cost appears). **Any future sweep here must assert that `out.bin` size
or a lowered-function count actually changes with the swept parameter** — flat
RSS on a vacuous corpus reads exactly like a refutation.

### What this means

The synthetic N-file × M-function corpus **cannot reach the regime** that grows
at 1 GB/min: it stays pinned at the ~157 MB floor, which is just the compiler's
own baseline. The mechanism therefore depends on something the synthetic corpus
does not contain — plausibly generics/traits/impls, dictionaries, cross-module
type resolution, or the sheer symbol-table size of the real compiler tree — not
on raw function or module *count*.

## Leading suspect (REFUTED as the memory mechanism — see above)

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

## Repro without a 60-minute build (ATTEMPTED — DOES NOT REPRODUCE)

**This section is retained for the record; the sweep it proposes was run and came
back flat. See "MEASURED 2026-08-10" above before spending time here.**


`build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple` (the binary that
compiles Stage-3) driving a small synthetic N-file `--entry-closure` chain with
`SIMPLE_BOOTSTRAP=1` and **`SIMPLE_BOOTSTRAP_STAGE4` unset**, sweeping
functions-per-file. The O(F²) hypothesis predicts peak RSS **quadratic in
functions-per-file** at fixed file count; a retention-only mechanism predicts
linear. Probe harness kept out of tree at
`<scratchpad>/probe.sh` (mirrors the STAGE4 guard's generator, minus
`SIMPLE_BOOTSTRAP_STAGE4=1`).

## Verdict

**Root cause NOT established**, and the previously-leading suspect is now
**refuted** by direct measurement (see "MEASURED 2026-08-10" above). The
discriminating sweep was completed and came back negative on both axes: peak RSS
is flat within 1% across 4x functions-per-file and 6x file count.

Two further facts constrain what remains:

1. **The real trace is LINEAR, not quadratic.** 26.5 GB @30 min → 52.5 GB @59
   min is a 1.98x RSS rise over a 1.97x time rise. Any *quadratic* accumulator
   (including the `arr = arr.push(x)` clone idiom) is the wrong shape for this
   curve regardless of the sweep. The mechanism is **constant retention per unit
   of work**, i.e. something allocated per item and simply never freed under the
   no-GC bootstrap runtime.
2. **`bootstrap_hir_functions_reset()` is per-module**, not per-run
   (`_Items/module_lowering.spl:2040`, gated only on `bootstrap_mode`), so
   `_bootstrap_hir_functions` is bounded by the largest single module. Only the
   seven `_bootstrap_hir_module_*` arrays survive across modules
   (`bootstrap_hir_modules_reset()` at `:1811` runs entry-module-only under
   `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1`) — and Sweep B shows growing the module
   count 6x does not move RSS.

**Next measurement:** stop using a synthetic corpus — it cannot leave the ~157 MB
floor. Instead compile a **real bounded subset of the compiler tree** (e.g.
`--entry-closure` from a mid-sized real module under `src/compiler/10.frontend/`),
with an RSS sampler at ~10 s and `SIMPLE_COMPILER_PHASE_PROFILE=1`, and bisect on
*source features* rather than counts: confirm growth appears, then remove
generics/traits/impls/dicts from the closure until the slope dies. The failed
sweeps prove the driver of the 1 GB/min is a **feature** of the real source, not
its size. Second-choice measurement if that is still too slow: attach
`heaptrack`/`massif` to a 5-minute prefix of the real Stage-3 run and read the
top retained allocation site directly — the growth is visible within minutes, so
a bounded prefix is sufficient and does not need the 60-minute run.

Still-unexcluded structural candidate (not yet tested, and NOT promoted to
"suspect" — it has no measurement behind it): the flat-AST arenas
`decl_*`/`stmt_*`/`expr_*` in `src/compiler/10.frontend/core/_Ast/`, which the
streaming driver clears via a **single** `ast_reset()` **after all modules are
lowered** (`src/compiler/80.driver/driver_hir_pipeline_lowering.spl:230`). This
retains every module's flat AST for the whole run and is linear in total source
size — the right *shape* for the observed curve. Sweep B did not move it, but
Sweep B's modules are trivial; per-module AST bytes, not module count, is the
quantity that matters.

## Follow-on work regardless of verdict

1. Add a Stage-3-lane (flat-bootstrap) analogue of
   `check-stage4-selfhost-parse-memory-multifile.shs`. The lane is currently
   unguarded for memory.
2. Replace the functional `arr = arr.push(x)` accumulator idiom in
   `lowering_helpers.spl` with an in-place append, or drop the global arrays in
   favour of reading the already-retained `HirModule`s.
3. Never read exit 143 from a `simple` process as a build failure without first
   excluding earlyoom.
