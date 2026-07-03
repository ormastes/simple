# draw_ir_adv_spec 2nd scenario fails on stale deployed binary — missing `rt_host_gpu_queue_reset` extern registration

**Status:** OPEN — not a source bug, deployment staleness only.
**Severity:** Low/local — only affects results produced by the currently
deployed `bin/release/aarch64-apple-darwin-macho/simple` on this workspace;
does not affect correctness of `draw_ir_adv.spl`, the spec, or `main`.
**Affected file (deploy artifact only):** `bin/release/aarch64-apple-darwin-macho/simple`
(dated 2026-06-06 15:14, i.e. ~4 weeks stale relative to HEAD).
**Spec file:** `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl`
**Path:** `bug` track (deploy/bootstrap staleness, not a code defect).

## Symptom

Running the spec with the currently deployed self-hosted binary:

```
SIMPLE_EXECUTION_MODE=interpret SIMPLE_EXECUTION_LIMIT=0 OSTYPE=darwin \
  bin/simple run test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl
```

gives 3 pass / 1 fail:

```
Engine2D advanced Draw IR executor
  ✓ executes a Draw IR batch through the Simple2D advanced interface with embedding offsets
  ✗ submits a GPU-selected Draw IR batch through the runtime host GPU queue
    semantic: unknown extern function: rt_host_gpu_queue_reset
  ✓ executes a composed Draw IR scene in batch order
  ✓ reports unsupported Draw IR commands without rendering them

4 examples, 1 failure
```

## Root cause (confirmed, not just inferred)

`bin/simple` → `bin/release/aarch64-apple-darwin-macho/simple`, a **statically
linked** binary (no `libsimple_runtime.dylib` dependency per `otool -L`) built
2026-06-06. The `rt_host_gpu_queue_*` extern dispatch arm in
`src/compiler_rust/compiler/src/interpreter_extern/mod.rs` (and the backing
`host_gpu_lane::rt_host_gpu_queue_reset` in
`interpreter_extern/host_gpu_lane.rs`) only became reliably present from the
`wip: sync active gpu gui and platform lanes` commit (`5efadacfc2`,
2026-06-14) onward — **after** the deployed binary was built. Because the
dispatch table is baked into the binary at compile time, the June-6 build
simply has no code path for this symbol name.

Verified two ways:

1. Isolated single-call probe (rules out anything specific to
   `draw_ir_adv.spl`/the spec):
   ```
   use std.gc_async_mut.gpu.engine2d.host_gpu_event_queue.{engine2d_host_gpu_runtime_reset}
   engine2d_host_gpu_runtime_reset()
   print("reset ok")
   ```
   - `bin/simple run probe.spl` (deployed Jun-6 binary) →
     `error: semantic: unknown extern function: rt_host_gpu_queue_reset`
   - `src/compiler_rust/target/bootstrap/simple run probe.spl` (Rust seed,
     freshly built today from current HEAD) → `reset ok`

2. Full spec against the fresh seed binary:
   ```
   SIMPLE_EXECUTION_MODE=interpret SIMPLE_EXECUTION_LIMIT=0 OSTYPE=darwin \
     src/compiler_rust/target/bootstrap/simple run test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl
   ```
   → `4 examples, 0 failures` — all four scenarios, including the
   `runtime host GPU queue` one, pass.

## Why this is not a test-vs-executor bug

Both the assertions in `draw_ir_adv_spec.spl` (scenario 2, lines 85-105) and
the executor code in `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl` /
`host_gpu_event_queue.spl` are correct against current HEAD — confirmed by
the 4/4 pass on a freshly built interpreter. The three other scenarios in the
same spec pass on the stale binary too, because they never call
`engine2d_host_gpu_runtime_reset()` → `rt_host_gpu_queue_reset`. This is
consistent with the recent memory note
`project_pure_simple_bootstrap_gui_verify_2026-06-15.md` and the 2026-07-01
commit `7241743871` ("blocked by stale compiled binary (bootstrap failure
prevents rebuild)") — the deployed platform binary on this workspace has been
known-stale for weeks and this is one more symptom of that same gap, not a
new defect.

## No source change made

Per repo policy, redeploying `bin/release/<triple>/simple` requires a full
`scripts/bootstrap/bootstrap-from-scratch.sh --deploy` + smoke gate (see
`.claude/rules/bootstrap.md`), which is out of scope for a single-spec
diagnosis and was previously observed to be non-trivial to get green (Stage-3
self-host = documented LIM-010; `--deploy` has no smoke gate and was
"Verified broken 2026-06-11"). No edits were made to `draw_ir_adv.spl` or
`draw_ir_adv_spec.spl` — both are correct. The nomirror/parity gates
(`scripts/check/check-engine2d-nomirror-fast-render-evidence.shs`,
`scripts/check/check-engine2d-cpu-metal-parity-evidence.shs`) were not
re-run since no source under their coverage changed.

## Suggested resolution

Re-run `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` (with the
mandatory post-deploy smoke test) to refresh
`bin/release/aarch64-apple-darwin-macho/simple` from current HEAD, once a
bootstrap window is available that isn't contended by concurrent agents. That
will close this and any other now-missing-extern symptoms from the same
staleness gap in one pass — no per-symbol patching needed.
