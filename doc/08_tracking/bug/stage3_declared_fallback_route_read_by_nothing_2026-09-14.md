# Stage 3 declares `fallback_route=direct` and nothing ever reads it (2026-09-14)

## Status

OPEN. The companion half of this defect — the unreachable
`SIMPLE_SCV_INVENTORY_COLD_INIT` remedy — is FIXED
(`scripts/bootstrap/resume-stage3-from-admitted.sh`, pinned by
`scripts/check/check-bootstrap-stage3-scv-cold-init-passthrough.shs`). This
record covers what remains.

## Symptom

F74 round 3, Stage 3 run 3 (coordinator route, `SIMPLE_NATIVE_BUILD_THREADS=5`)
failed in ~2 minutes with:

```
SCV-E-ADMISSION: compile-event-journal-missing
(first build in this checkout: rerun with SIMPLE_SCV_INVENTORY_COLD_INIT=1)
```

The run's own status receipt recorded `requested_route=coordinator
fallback_route=direct`. The direct route was never attempted. The run simply
failed.

## Root cause

`scripts/bootstrap/resume-stage3-from-admitted.sh` computes
`stage3_fallback_route=direct` whenever `stage3_threads > 1` and exports it as
`SIMPLE_BOOTSTRAP_STAGE3_FALLBACK_ROUTE`. Verified 2026-09-14 at
`2ecbe35baf7`:

```
$ /usr/bin/grep -rn 'STAGE3_FALLBACK_ROUTE' src scripts
scripts/bootstrap/resume-stage3-from-admitted.sh:617   (args digest)
scripts/bootstrap/resume-stage3-from-admitted.sh:648   (transcribed invocation)
scripts/check/check-bootstrap-stage2-struct-receiver.shs:143
```

Zero readers under `src/`. By contrast
`SIMPLE_BOOTSTRAP_STAGE3_REQUESTED_ROUTE` **is** read, at
`src/app/cli/bootstrap_main.spl:411`, and does select the route. The fallback
is declarative metadata written into a receipt and consumed by nothing — it
describes an intention that no code implements.

## Why it was not fixed in the same change

The coordinator route enters `run_bootstrap_stage3_process_route`
(`src/app/cli/bootstrap_main.spl:172`), which returns a bare `i64` from
`run_native_build_worker`. There is no distinguished exit status for "the SCV
admission precondition refused me" as opposed to "the build failed", so an
in-process fallback cannot currently tell the two apart — and falling back on
*any* non-zero status would silently convert a real compile failure into a
slow, serial retry that then fails again, hiding the first error. Making the
fallback honest needs a typed admission-refusal status crossing that boundary;
that is a design change, not a one-line fix.

The cold-init pass-through removes the *observed* trigger (the coordinator
route can now be told to cold-init), so the fallback is no longer the only way
out of this particular refusal.

## Required fix (not done)

Either:

1. give `run_bootstrap_stage3_process_route` a typed refusal result so the
   caller can distinguish an admission precondition from a build failure, and
   route only that class to the direct path, recording
   `fallback_fired=admission-precondition` in the Stage-3 status receipt; or
2. delete `SIMPLE_BOOTSTRAP_STAGE3_FALLBACK_ROUTE` entirely, so the receipt
   stops promising a behaviour the system does not have.

Do NOT leave it as it is. A receipt field that records a fallback which cannot
fire is worse than no field: it was read as reassurance during the F74 lane and
cost a diagnosis cycle.

## Evidence

- `build/f74_status.txt`, "F74 r3 STAGE3 RUN3" and "RUN4" blocks.
- `build/f74logs/stage3-run3.log`, `stage3-run4.log`.
- Raiser: `src/app/compiler_entrypoint/inventory_events.spl:198-207`.
- Consumer of the *requested* route: `src/app/cli/bootstrap_main.spl:405-412`.
