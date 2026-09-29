# Windows pre-push gates blocked by host toolchain skew (SPIR-V pin) + stale-lock recovery gap

Date: 2026-09-19
Status: OPEN — blocks ANY push from this Windows host whose tree contains
current `main` content (both findings are content-independent of the pushed
branch).
Lane: push gates, work/image-memory-budget-20260915 campaign.

## Finding 1 — `push-rect-batch-spirv-pinned` cannot pass on this host

Gate: `scripts/check/check-rect-batch-spirv-pinned.shs` (BLOCKING in
`check-push-must-pass.shs`). Recompiles
`src/lib/gc_async_mut/gpu/engine2d/shaders/rect_batch.comp` with the
PUSHING host's `glslangValidator` and byte-compares against the words pinned
in `backend_vulkan_rect_batch_spirv.spl` (pinned 2026-09-11 in beb45c038b3).

Measured 2026-09-19: committed 5848 bytes vs freshly compiled 5836 bytes.

- The `.comp`, the pinned `.spl`, `spirv-to-spl-words.shs`, and
  `gen-rect-batch-spirv.shs` are all unchanged since beb45c038b3, and
  identical between `origin/main` and the pushed branch — the pushed content
  did not cause the delta.
- The delta is glslangValidator VERSION skew: the pin was produced with the
  scoop `glslang` 7.11.3214-era validator (this host had it until the scoop
  update to 8.13.3559 on 2026-09-17, two days after the pin); the installed
  validator now self-reports internal version 11.13.0 and emits different
  bytes for the same GLSL.
- Attempted locally: downloaded the 7.11.3214 release build; it requires
  MSVCR120.dll (VC++ 2013 redist), which is absent system-wide and could not
  be extracted portably from the redist bundle without MSI machinery.

Consequence: until either (a) a runnable validator matching the pin is
present, (b) the pin is regenerated with a repo-pinned canonical glslang
version (the gate should arguably pin/record the expected validator version
— today it does not), or (c) the gate gains a sanctioned toolchain-version
tolerance, no push of current `main` content can pass from this host.

## Finding 2 — `portable_lock` stale recovery never fires on this host

`scripts/check/lib/portable-process-lock.shs` (`portable_lock_acquire` /
`portable_lock_recover_stale`) is supposed to detect a dead owner pid and
recover the lock. Measured 2026-09-19: after killing a bootstrap
(`TaskStop`, children SIGKILLed), TWO locks held by the dead pid 633396 —
the bootstrap output lock (`.simple/storage/build/.simple-bootstrap-locks`)
and the Rust authority lock
(`src/compiler_rust/target/.bootstrap-authority-locks/.authority.lock`) —
were never recovered; two subsequent bootstrap attempts aborted on
"timed out waiting for ..." until the stale lock files were removed by hand.

Likely cause: the liveness probe (`portable_lock_claim_state`) relies on
pid/start-time inspection that fails open-to-"alive" on this MSYS/Git-Bash
host (MSYS pids are not Windows pids; `tasklist` cannot see them; the
probe's ps/proc path returns nothing useful). The recovery path is
therefore dead code here, and every killed holder requires manual lock
cleanup before the next bootstrap/push attempt.

Consequence: any killed bootstrap/runner on this host wedges the output
dir and the Rust authority for every later attempt until manual cleanup.

## Workarounds in use

- Push carries on with the C-runtime gate green (5 POSIX selfcheck TUs fixed
  to parse on Windows in 9c6f6874088 — that part was a genuine defect, now
  fixed: gate reports 134 compiled / 0 errors).
- Remaining blockers at push time: ONLY the SPIR-V pin gate (everything
  else in the manifest passed on 2026-09-19, including conflict-tree,
  tree-size, conflict-markers, merge-content-conservation, runtime-api
  regression, interpreter-extern-registry, windows-checkout-damage,
  main-test-runnable, symbol baselines; several advisory gates recorded
  their verdicts).
