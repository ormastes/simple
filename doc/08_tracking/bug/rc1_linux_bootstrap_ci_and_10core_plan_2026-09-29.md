# RC1 Linux bootstrap CI and ten-core plan

Date: 2026-09-29. Release branch head at inspection:
`96c901e0130d3dd4f6d2528e47532e040ff6ef7e`.

## Completed CI evidence

- AOT Lane Fences run `36499845538`, job `109187904439`, used release commit
  `42ea10e42a899f1dc58d60e76c8de076add0ede3`. Stage 2 was admitted at
  00:30:42 UTC; the planner receipt was produced at 00:30:51; both native
  cache ownership checks passed by 00:30:58. At 00:36:40 the log says
  `Killed`, followed by `The operation was canceled`. The Stage 3 step is
  marked **cancelled**, and the failure-log upload was skipped. There is no
  compiler diagnostic or explicit runner-shutdown message in this job log,
  so the kill cause is unproven. Log:
  `/tmp/rc1-linux-release-job-109187904439.log` (lines 1616–1627).
- The synthetic same-source AOT job `109187701569` also reached an admitted
  Stage 2 and planner receipt before a documented runner shutdown signal.
  Its log is `/tmp/rc1-linux-pr-job-109187701569.log`. Neither terminated run
  proves a Stage 3 compiler failure.
- The release head's Rust Bootstrap Multiplatform Linux LLVM job
  `109192601518` stopped before bootstrap in
  `scripts/check/check-bootstrap-portability.shs`: `FAIL: FreeBSD full
  execution wiring missing`. Log:
  `/tmp/rc1-linux-rust-bootstrap-job-109192601518.log`.
- The release head's Linux Cranelift job `109192601656` reached bootstrap and
  exited 64 with `bootstrap-policy-error: reason-receipt-required`. The shared
  workflow owner is preparing the typed Stage 2 receipt and Stage 3 resume
  path. Log: `/tmp/rc1-linux-cranelift-job-109192601656.log`.

## Portability guard proposal and limit

The reviewed FreeBSD workflow intentionally checks offline media refusal on
unprovisioned GitHub runners. Full QEMU proof requires an admitted local VM
image and digest. This branch updates the stale guard to require that refusal,
reject false VM claims, recognize the wrapper's receipt-bound Stage 2/3/4
commands, and distinguish an executable `curl`/`wget` fetch from `curl` in the
guest package list. Focused regex fixtures detected an indented `curl`, an
indented conditional `wget`, and allowed `pkg install ... curl ...`.

Three bounded full guard cycles advanced through those stale assertions, but
the third stopped at a separate old expectation:
`text index_of absence must return canonical Option.None`. It searches for
`return rt_enum_new(1, 1, 3)`, while current
`src/runtime/simple_core/core_string.spl` uses the SFFI facade
`return _sffi_rt_enum_new(1, 1, 3)`. This branch does not change that
assertion. Logs: `/tmp/release-rc1-bootstrap-portability-fixed.log`,
`/tmp/release-rc1-bootstrap-portability-fixed-cycle2.log`, and
`/tmp/release-rc1-bootstrap-portability-fixed-cycle3.log`. **The full guard is
not green; this branch is not a release qualification.** A fresh scoped
follow-up must validate the facade's semantics and repair that assertion.

## Next Linux invocation with ten cores

The local Linux host exposed 20 allowed CPUs (`0–19`) and 121 GiB RAM at the
checkpoint. It had only 65 GiB disk space free; check disk headroom again
before any build. The GitHub Linux runner in the failed AOT run exposed only
four CPUs, so a request for ten cores needs a larger runner or this local
host. The default `incremental` profile caps self-host work at two threads
even when `--jobs=10` is passed. Once a fresh session authorizes a new
candidate run and the remaining gates are repaired, the bounded **Stage 2**
invocation on this host is:

```sh
timeout 5400 taskset -c 0-9 env SIMPLE_BOOTSTRAP_EXECUTION_PROFILE=incremental-unlimited \
  sh scripts/bootstrap/bootstrap-from-scratch.sh --backend=llvm --mode=dynload \
  --full-bootstrap --stop-after-stage2 --no-mcp --jobs=10
```

The canonical admitted Stage 3 resume rejects `--jobs>1` and pins its native
recompile to `--threads 1` in `resume-stage3-from-admitted.sh`. A ten-worker
Stage 3 would need a separately reviewed scheduler/provenance change; changing
the workflow flag alone cannot achieve it. Do not restart a capped full local
bootstrap solely to vary worker count. Preserve the Stage 2 artifact, produce
the typed planner receipt for its exact parent, and resume Stage 3 under the
current one-worker contract once the candidate is ready.
