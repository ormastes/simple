# Stage-2 sanity, `SIMPLE_BOOTSTRAP=1` pass: backend object emission returns status 1 with an EMPTY diagnostic

- Status: OPEN (2026-09-13)
- Found: bootstrap lane BOOT-5, `work/bootstrap-full-3-2026-09-12` rebased onto
  `origin/main` `3a3e0121a7e`
- Severity: **the current Stage-2 admission blocker on Linux aarch64.** It is the
  first blocker in this chain that lands in the `SIMPLE_BOOTSTRAP=1` pass with
  the `SIMPLE_BOOTSTRAP=0` pass fully green.

## Verdict, verbatim

```
error: sanity FAIL - frontend smoke exited 1 (bootstrap-mode pass: 1)
bootstrap-sanity-error: version_status=0 version_output=simple-bootstrap 1.0.1-beta.1 unsupported_status=1 frontend_status=1 candidate_unchanged=true
candidate_frontend_smoke: hello-world-positional-build failed (raw rc=1)
  reason: AOT compile error in scripts.check.cert.redeploy_gate.fixtures.hello_world:
    backend object-path status 1 (diagnostic file empty; path .../simple-aot-diagnostic-96Lzfe/message)
error: Stage 2 bootstrap compiler sanity failed
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

Stage 2 itself built and linked clean:

```
Build complete: 886 compiled, 0 cached, 0 failed
Linked: .../bootstrap-boot5c/stage2/aarch64-unknown-linux-gnu/simple (148632 KB) via clang++
```

Candidate (preserved, not deployed):
`build/bootstrap-boot5c/stage2/aarch64-unknown-linux-gnu/simple.rejected`,
sha256 `67786227817bf45f...`.

## The control is inside the same run

`(bootstrap-mode pass: 1)` names the failing pass. The `SIMPLE_BOOTSTRAP=0` pass
ran the identical positional probe on the identical binary and **succeeded** —
its log ends with advisory canary lines and no `ERROR=` summary. So this is a
`SIMPLE_BOOTSTRAP`-dependent defect, the same family as the three sites already
fixed, and NOT the platform-independent capsule defect.

This is also the first time in the BOOT-3/4/5 chain that the
`SIMPLE_BOOTSTRAP=0` pass passes end to end.

## What "status 1, diagnostic file empty" means

`driver_aot_native_output.spl:2470-2495` says it itself: every failure path in
the backend writes a diagnostic (`compile_ir_to_object_path`,
`llvm_object_stage_fail`), so an empty one means **either the write did not land
or this read could not see it** — and the code deliberately names which of the
two it observed, because "status 1" alone could not tell them apart. Here it
read the file and found it zero-length (`diagnostic file empty`), not missing
and not unreadable.

So the next lane has two candidates and a cheap way to separate them:
1. the backend really failed and its diagnostic write was lost (a write/flush or
   staging-directory lifetime problem), or
2. the backend did not fail and `status` is itself wrong under bootstrap mode.

Note the `[receipt-size-canary]` lines in BOTH passes of this run
(`field=169079505 / 174382545 / 457343569` vs `runtime=1080`): an
optional-bound scalar field read IS miscompiled in this binary. A `status`
read through a similar binding is squarely in that blast radius, which makes
candidate 2 worth testing before candidate 1.

## Relationship to the other records

- `bootstrap_mode_assumes_bootstrap_cli_probe_chain_2026-09-13.md` — sites 1-3,
  FIXED. `MIR module has no functions` no longer occurs in any pass; this
  failure is two phases later, in the backend.
- `stage2_capsule_receipt_size_canary_blocks_linux_admission_2026-09-13.md` —
  site 4, fixed upstream by `7e8090f10c2` (PR #712). Confirmed working here: the
  canary now REPORTS and does not fail the build, which is precisely why this
  run got far enough to expose the present defect.
- `stage2_sanity_dies_on_unset_compiler_build_timeout_seconds_2026-09-13.md` —
  an unrelated abort that must be avoided (do not set
  `COMPILER_BUILD_TIMEOUT_SECONDS`) to reach this point at all.

## Reproduction

    cd /home/yoon/dev/simple-boot5   # or any worktree at origin/main 3a3e0121a7e
    sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap \
      --backend=llvm --mode=dynload --jobs=10 --stop-after-stage2 --output=<fresh>
    # do NOT set COMPILER_BUILD_TIMEOUT_SECONDS
    cat <fresh>/stage3/<triple>/stage2-sanity.env.frontend-bootstrap-1.log.hello-world-positional

Faster, against the preserved candidate (~30 s, no bootstrap), with
`SIMPLE_BOOTSTRAP` as the only variable:

    CAND_OVERRIDE=<...>/bootstrap-boot5c/stage2/<triple>/simple.rejected \
      sh scratchpad/boot5/disc5.sh bs0_trace bs1_new
