# Stage 2 receiver probe intermittently reports `compiler.common.module_path_naming` as NOT_RUN

- **Filed:** 2026-09-14
- **Status:** OPEN — 2 failures in 3 runs, across two different trees (2026-11-11 lane boot18: attribution defect FIXED and verified on seed; underlying transient stays OPEN, not reproducible in this lane — see addendum)
- **Severity:** blocks a bootstrap lane non-deterministically

## Symptom

The Stage 2 trust-root lane

```
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 \
   --mode=dynload --jobs=half --produce-stage3-receipt=verify-landed-compiler-fix
```

fails its receiver probe with

```
error: stage2 failed the positional pure-Simple Stage-3 route (status 1)
error: in-process native-build: build failed: 0 failed, 0 unverified, 1 not run,
       1 ok of 2 unit(s) — NOT_RUN: compiler.common.module_path_naming
```

and the lane exits 3: `--stop-after-stage2 requires a successful admitted Stage 2 compiler`.

Observed runs (F74 round 3, macOS arm64): run 1 `def2a9c30a1` FAIL, run 2
`def2a9c30a1` PASS, run 3 `4f4d0e12832` FAIL, run 4 `4f4d0e12832` PASS. Same
command, same host. Re-running is currently the only workaround.

## Mechanism — bookkeeping, not a scheduling race

`stage2-receiver.log` shows the build is **sequential**, which makes the
recorded reason ("never started (build ended first)",
`src/compiler/80.driver/driver_build/build_outcome.spl:257`) hard to take at
face value:

```
[build] phase=native_compile state=running ... done=0 total=2 ... current=compiler.common.module_path_naming
[NATIVE] codegen: 2 uncached module(s), concurrency=1 (build() compiles modules sequentially in this process)
find_llc: ... resolved=[/opt/homebrew/opt/llvm@18/bin/llc]
find_llc: ... resolved=[/opt/homebrew/opt/llvm@18/bin/llc]
===== build outcome summary =====
OK=1  ERROR=0  CRASHED=0  TERMINATED=0  TIMEOUT=0  NOT_RUN=1
  - compiler.common.module_path_naming
      reason: never started (build ended first)
```

`llc` is resolved **twice**, once per module, so both modules were processed —
yet one outcome is `OK` and the other defaults to `NOT_RUN`. With concurrency 1
and sequential compilation, a genuine "build ended first" race is unlikely. The
more probable defect is an **outcome that is never recorded**, leaving the unit
at its `NOT_RUN` default. The unit that loses its outcome is the one that was
`current` when `native_compile` began.

## Do not relax the probe

`0 failed, 1 not run` means the build did not run everything it planned. The
probe is correct to refuse it. The fix belongs in the outcome bookkeeping, not
in the gate. Not bisected; no repro smaller than the lane itself.

## 2026-09-14 — attribution defect RESOLVED; the transient stays OPEN

Two defects were tangled here. The **misattribution** is fixed; the **underlying
transient** is not, and this record stays OPEN for it.

### Mechanism (the part now fixed)

`src/compiler/80.driver/driver_aot_native_output.spl`, the native post-process
loop over `uncached_names`. It re-derived each unit's outcome from a SECOND
evaluation of the capsule receipt invariant:

```
if capsule.ok and driver_native_capsule_result_valid_v1(capsule):   # -> OK
elif not module_outcomes.has_path(name):                            # -> NOT_RUN
```

The `elif` collapsed two different things into one verdict:

- (a) the compile phase genuinely never reached the unit, and
- (b) the compile phase DID run it — `driver_native_collect_capsule_result_v1`,
  the owner-only authenticated checkpoint, accepted its capsule (hence
  `0 failed`) — and this later re-check rejected it.

(b) was reported as `NOT_RUN: never started (build ended first)`, which is false:
`llc` resolved once per module, so both units started. Worse, the ONE diagnosable
fact — `driver_native_capsule_result_reason_v1`, computed on that very line —
was discarded. That is why the lane could only ever report the name.

Fix (this change):

- `module_units_attempted` records the compile phase's OWN dispatch ledger
  (`stats.completed + stats.failed` on the ParallelBuilder path, `1` on the
  single-module direct path).
- `driver_native_attempted_unit_failure_detail_v1` decides between the two:
  an attempted unit is recorded FAILED **naming the invariant that fired**;
  NOT_RUN is reserved for `attempted < scheduled`, unchanged and still
  fail-closed.
- The receipt invariant is now evaluated **exactly once** per unit. Deciding
  with `..._valid_v1` and then re-deriving with `..._reason_v1` read the same
  mutable state twice; if it differed between the two reads — the very
  instability being reported — the recorded reason came back empty.

Spec: `test/01_unit/compiler/driver/native_attempted_unit_outcome_recorded_spec.spl`
(4 examples; sabotaging the `attempted < scheduled` guard turns 3 of them red).

### What this does and does not change

It does **not** make the probe pass. A recurrence still fails the build at the
same rate; it now fails NAMING the invariant, e.g.

```
[native-compile-failed] compiler.common.module_path_naming: compiled unit has
no usable capsule result: <source-identity-mismatch|receipt-content-mismatch|
object-missing|...>
```

instead of `never started (build ended first)`. The probe is not relaxed.

### Not reproduced here

The real probe could not be run on this host: the tracked
`bootstrap/stage2/aarch64-apple-darwin-macho/simple` is the 126 KB bootstrap-stub
CLI and answers `bootstrap_main cannot emit a seed-wrapper fallback ... rebuild
with the full Simple driver`. Producing a real Stage 2 artifact IS the ~90 min
lane. So "10/10 after the fix" is **not verified**; only the attribution change
is verified, by spec.

### Prediction for the next recurrence

Given `native_capsule_source_identity_survives_eviction_spec.spl` (a prior
incident where a capsule's text identity was reclaimed and only surfaced on a
later look), the most likely named invariant is `source-identity-empty` or
`source-identity-mismatch` on `uncached_names[0]` — the unit that was `current`
when `native_compile` began. Whoever hits this next: paste the
`[native-compile-failed]` line into this record. It will confirm or refute that
in one run.


## 2026-11-11 addendum (lane boot18, work/p3-boot18-20261111) — attribution FIXED; transient stays OPEN

Triage of the base+flake pair (together with
`stage2_receiver_probe_module_path_naming_not_run_flake_2026-09-14.md`). The
2026-09-14 attribution defect recorded in this doc is FIXED and verified; the
underlying transient is NOT reproducible in this lane and stays OPEN, so the
Status line above remains OPEN.

Verified on the tracked seed `46fe8f6b6def` (`SIMPLE_LIB=src`, `--mode=interpreter
--no-cache`):
- `test/01_unit/compiler/driver/native_attempted_unit_outcome_recorded_spec.spl`
  **4/4 GREEN** — the attempted-unit ledger (`module_units_attempted`,
  `driver_native_attempted_unit_failure_detail_v1`) is present in
  `driver_aot_native_output.spl:833,2626-2885`; NOT_RUN is now reserved for
  `attempted < scheduled`, and an attempted unit that fails the capsule
  invariant is recorded FAILED naming the invariant (`capsule-identity-empty`,
  `native-capsule-source-mutated`, `native-capsule-receipt-invalid`, fsync
  variants) instead of the false "never started (build ended first)".
- `test/01_unit/compiler/driver/native_capsule_source_identity_survives_eviction_spec.spl`
  **7/7 GREEN** — the frozen capsule identity is the phase-1 recorded identity,
  not a re-hash of already-evicted content (the site-10 root cause).

Why the transient still stays OPEN: the site-10 identity fix predates these
failures (site 10 = 2026-09-12; this record = 2026-09-14), so it did not
prevent them. This doc's own prediction for a recurrence —
`source-identity-empty` / `source-identity-mismatch` on `uncached_names[0]`, the
unit that was `current` when `native_compile` began — has no in-lane repro (the
doc: "no repro smaller than the lane itself"; end-to-end is the ~90 min Stage-2
trust-root lane, outside this triage lane's budget/grant). Next owner with a
live failure: paste the `[native-compile-failed]` line here; the named invariant
will confirm or refute the prediction in one run. Do not relax the probe.
