# CudaLaneSession.create() unresolved across module boundary (blocks B2 live verification)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

Date: 2026-08-07
Filed by: Task B2 (cuda_jit lane executor), `doc/03_plan/agent_tasks/gpu_remote_interpreter_parallel_plan_2026-08-07.md`

## Symptom

Calling `CudaLaneSession.create()` (the B1-landed static factory in
`src/lib/gc_async_mut/gpu_lane/cuda_lane_session.spl`) from ANY other module —
including the new B2 `CudaJitLaneExecutor.create()` in
`src/lib/gc_async_mut/gpu_lane/cuda_jit_lane_executor.spl`, and a minimal
one-line repro below — fails to resolve on this host, under both engines
`bin/simple` currently dispatches to:

- `bin/simple test test/03_system/gpu_lane/cuda_jit_hello_spec.spl`:
  `semantic: variable \`CudaLaneSession\` not found` (tree-walk interpreter
  path used by the test runner).
- `bin/simple run build/tmp/probe_cuda_lane.spl` (minimal repro below):
  `Runtime error: Function 'create' not found` /
  `Runtime error: unresolved symbol -- this is a code-generation dispatch gap,
  not a program error.` (JIT path).

The import itself (`use
std.gc_async_mut.gpu_lane.cuda_lane_session.{CudaLaneSession}`) is byte-for-byte
identical to the one B1's own already-landed spec
(`test/02_integration/gpu_lane/cuda_lane_session_spec.spl`) uses successfully in
its own describe blocks -- so this is not an import-path typo.

## Evidence this is a deployed-binary/environment issue, not a B1/B2 code defect

1. **Minimal repro** (`build/tmp/probe_cuda_lane.spl`, 4 lines):
   ```
   use std.gc_async_mut.gpu_lane.cuda_lane_session.{CudaLaneSession}

   fn main():
       val s = CudaLaneSession.create()
       print(s.probe())
   ```
   `bin/simple run` on this: `Runtime error: Function 'create' not found`.

2. **B1's own pre-existing spec, unmodified, now ALSO fails** --
   `bin/simple test test/02_integration/gpu_lane/cuda_lane_session_spec.spl`
   returns `error: no \`main\` function and no top-level statements: this
   module declares only names, so running it would execute nothing` /
   `error: test-runner: no examples executed` -- a DIFFERENT failure mode than
   the one above, on a file that (per the B2 task briefing) was already landed
   and previously verified working. Two unrelated failure modes on two
   different files in the same dependency family, on the same host, in the
   same session, is a strong signal the *deployed binary itself* is unstable
   right now, not that either spec regressed.

3. `bin/simple --version` currently prints:
   ```
   WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use
   it as the normal tool.
   Build and use the pure-Simple bin/simple instead.
   ```
   i.e. `bin/simple` (-> `bin/release/x86_64-unknown-linux-gnu/simple`) is
   currently the Rust seed, not the mandated pure-Simple self-hosted binary
   (see `.claude/rules/bootstrap.md`, memory
   `reference_bin_simple_symlink_stale_scratch_build_and_verify_binary_provenance`).
   `bin/release/simple` (the production wrapper script) independently refuses
   to run it: `error: refusing non-production Simple runtime:
   /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple`.
   `bootstrap/stage3/x86_64-unknown-linux-gnu/simple` exists (built
   2026-08-07 11:28, stripped, 3.4MB, no seed-warning banner) but is a
   bootstrap-verification binary only -- it has no `test`/`run` subcommands
   (`error: unknown command 'test'`) and cannot substitute.

## Impact on Task B2

Blocks the live half of `test/03_system/gpu_lane/cuda_jit_hello_spec.spl`'s
"vector-add hello dispatch" example (`CudaJitLaneExecutor.create()` ->
`CudaLaneSession.create()`). All host-independent logic in the same spec file
passes cleanly under the current binary: the ten-row CUDA validation table
(10/10), lane-log recording (2/2), and the valid-PTX control case (1/1) -- 13
of 14 examples green. Sabotage-probed (removed the nonexistent-entry check,
confirmed rows 8+10 go RED, restored, confirmed GREEN again) -- see task
report. Left as a genuine RED example rather than weakened, per
`.claude/rules/testing.md`.

## Unblock condition

Rebuild/redeploy the production self-hosted `bin/release/x86_64-unknown-linux-gnu/simple`
(full `bin/simple build bootstrap` or the session that broke it redeploying its
result), then re-run:
```
bin/simple run build/tmp/probe_cuda_lane.spl
bin/simple test test/02_integration/gpu_lane/cuda_lane_session_spec.spl
bin/simple test test/03_system/gpu_lane/cuda_jit_hello_spec.spl
```
If `CudaLaneSession.create()` still fails to resolve on a genuinely
self-hosted deployed binary, this becomes a real B1/B2 code defect and should
be re-triaged as such (not an environment issue).
