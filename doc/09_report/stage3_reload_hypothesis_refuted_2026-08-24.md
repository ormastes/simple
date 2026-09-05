# Lane X: the "692 x closure reload" hypothesis is FALSE — measured, 2026-08-24

Tests W's recorded-but-unverified reconciliation: *"Stage-3 is ~692 separate
`compile` invocations, each re-parsing the same ~750-module closure at ~21 s
each (692 x 21 s ~= 4 h)."*

## Verdict: NOT REPRODUCED. Stage 3 is ONE process that loads and parses the
## closure EXACTLY ONCE.

## Evidence

**Structural.** `scripts/bootstrap/bootstrap-from-scratch.sh:1271-1300`,
`bootstrap_native_build_main()`: stage 3 is a **single** `native-build`
invocation — `--mode one-binary --entry ... --threads N --entry-closure`. There
is no shell loop over modules. Per-module work happens in-process.

**Empirical**, from the real stage-3 phase-profile log
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
(403,564 B, 2026-08-20 23:57; `SIMPLE_COMPILER_PHASE_PROFILE=1`). Every line in
this log is duplicated (stdout+stderr both captured), so all raw counts below
are exactly 2x and are halved:

| event | raw count | actual |
|---|---|---|
| `compile:start` | 2 | **1** |
| `phase1:load_sources:closure:start` | 2 | **1** |
| `phase3:hir:file:start` events | 176 | 88 |
| distinct modules in those events | 88 | **88** |

One compile. One closure load. Each module lowered exactly once (88 events over
88 distinct modules — a re-parse loop would show events >> distinct).

## Where the time actually goes (single process, cumulative +ms markers)

| phase | window | duration | note |
|---|---|---|---|
| phase1 `load_sources` | +0 → +3,182 ms | **3.2 s** | closure scan of **614** files done at +1,128 ms |
| phase2 `parse` | +3,182 → +119,592 ms | **116.4 s** | all 614 modules, ~190 ms/module |
| phase3 `hir` | +119,592 → (log ends +269,000 ms) | **>149 s for 87/614 files** | ~1.7 s/file avg |

Per-file HIR deltas (86 measured): min 23 ms, max 4,364 ms, block averages
0.86-3.4 s with no clean superlinear trend — noisy but roughly flat.
Extrapolating 614 files at the observed average projects **~1,050-1,400 s for
phase 3 alone**, before typecheck/MIR/codegen/link.

Loading and parsing the entire closure costs **119.6 s, once**. That is ~8% of
the projected phase-3 cost and cannot be the multi-hour term. Per-module
`phase3:hir:imports:start`/`:done` pairs are emitted with **no ms delta at all**
— import resolution inside HIR is not re-reading source.

## The resume/admission lane is NOT a per-module loop either

Checked because it was the most plausible home for a literal "692": it pins
`--threads 1` and takes an "admitted" input, which reads like a per-module
recompile list. It is not. In `scripts/bootstrap/resume-stage3-from-admitted.sh`
"admitted" is an admitted stage-2 **binary** (`$stage3/stage2-admitted/simple`,
SHA-verified at :86-89), and the script issues 2-3 whole-closure `native-build`
invocations (:107, :119, :270, :292) — no loop over modules anywhere. The four
`build/bootstrap/admission/*/planner-source-closure.snapshot` files hold **4-5
lines each**, not ~692, and the string 692 appears nowhere in the admission or
progress records. **The number 692 has no located source in this tree.**

## Consequences

- The 692x-reload premise is dead. There is nothing to cache across
  invocations, because there are no repeated invocations.
- **No cross-invocation parse cache should be built.** Tasks 2 and 3 of this
  lane (inventory `interface_digest_of` / `smf_manifest_entry_verifies` /
  `object_cache_key`, then wire one) were conditional on verification and are
  therefore NOT started. Wiring a cache here would be speculative work against a
  refuted premise.
- The genuine cost center is **phase 3 HIR lowering at ~1.7-3.4 s per file**,
  ~10x the per-file parse cost. That is the only thing worth investigating next,
  and it is an intra-process, per-module cost — not a loading problem, not a
  closure-size problem, and (per W) not a duplication or barrel problem.

## What this does NOT explain

The 4-hour wall-clock observation is **not accounted for** — only the proposed
mechanism is ruled out. This lane's own arithmetic reconciles to ~25 minutes
(116 s parse + ~1,400 s projected HIR), an order of magnitude short. The
remaining time must live in post-HIR phases (typecheck / MIR / codegen / link),
all of them entirely unmeasured here, or in per-file HIR cost growing past file
87 — the last measured block averages 3.4 s/file against 1.7 s in the first, so
"roughly flat" is generous on 87 of 614 points. Do not read "refuted" as
"explained". Measuring a stage-3 run to completion with
`SIMPLE_COMPILER_PHASE_PROFILE=1` and reading the post-HIR phase boundaries is
the obvious next step, and was not done here.

## Honest limits
- The log is from an aborted/truncated run (ends mid-phase-3 at +269 s), so the
  phase-3 total is an extrapolation, not a measurement. Phases after HIR are
  entirely unmeasured.
- Its entry is `src/app/cli/bootstrap_main.spl` (614-file closure). Stage 4 uses
  `src/app/cli/main.spl`, a larger closure; these numbers are stage-3's.
- The truncation cause was not established: `dmesg` is unavailable to this user
  and the current `bootstrap-progress.log` describes a *different*, later
  attempt that died at `exit-101` in `rust-seed-build` (the local E0433 seed
  staleness W recorded, already fixed at origin) — it never reached stage 3.
- No code was changed and no fix was landed. Negative result; this document is
  the deliverable.
