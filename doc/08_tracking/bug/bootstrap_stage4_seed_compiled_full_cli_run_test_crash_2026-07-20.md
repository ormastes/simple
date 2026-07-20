# Stage-4 seed-compiled full CLI: run/test SIGSEGV at startup (Windows branch on Linux, tagged-value deref)

- **ID:** bootstrap_stage4_seed_compiled_full_cli_run_test_crash_2026-07-20
- **Status:** OPEN
- **Severity:** critical (single defect now gating the entire self-hosted redeploy)
- **Lane:** seed-compiled stage-4 full CLI (cranelift, core-c-bootstrap runtime lane)

## Context
After peeling five walls (LLVM-less seed, stale archive, sanitize collision,
self-host memory blowup, three backfill-class link defects), stage 4 BUILT
successfully for the first time: 47MB binary, sha256 6d587c4bf68a…, builds in
169s, reports `Simple v1.0.0-beta` with **no seed warning**, warm startup
0.00s/9MB, and `-c "print(1+1)"` → 2 works.

## Symptom
Every `run` and `test` invocation crashes at startup: **SIGSEGV rc=139**,
`SEGV_MAPERR si_addr=0x3c194581` (tagged-value-shaped address deref). Before
the crash the binary takes the **Windows platform branch on Linux** and fails
reading `/proc/meminfo`. The `simple_seed` delegate does not rescue it.

Smoke matrix: strictly worse than seed on all 9 specs (every one SIGSEGV vs
seed's mixed pass/fail/timeout baseline) → deploy refused by the
extended-smoke rule; deployed seed left untouched.

## Repro
`/tmp/wt_deploy/build/bootstrap/full/x86_64-unknown-linux-gnu/simple run <any.spl>`
(worktree kept with all native objects, logs in `stage4-seed-build.log`,
`smoke_new/`).

## Leads (in suggested order)
1. Platform-detection marshaling on the core-c lane: the Windows-branch-on-Linux
   selection suggests an extern returning a corrupted value at startup —
   check `rt_env_get` / `rt_file_read_text` value marshaling on the
   core-c-bootstrap lane first (same class as prior EXTERN_DISPATCH landmines).
2. The si_addr looks like a tagged value dereferenced as a pointer — consistent
   with a boxed/tagged return being passed unadapted across the C boundary.
3. gdb with the kept native objects in /tmp/wt_deploy.

## Cannot-adjudicate note
Fat32Core.new abort and REQ-015 (font_renderer TTF crash/timeout) remain
un-adjudicated on self-hosted until this startup crash is fixed.
