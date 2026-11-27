# Per-file native-build lane: MIR projected ownership missing HIR for app.cli._* on full-CLI closure (2026-11-12)

Lane: goal-mode bootstrap lane, worktree /home/yoon/dev/simple-boot-goal-20261112.
Producer: frozen stage2-admitted compiler sha256 574c95d29a8dc301ca7e13bb406cb962170774b6ece088d825eeb022eb95568d
(fable-16 lane, pinned source c7431e088615), backend cranelift, target aarch64-unknown-linux-gnu,
mode dynload, per-file pipeline default (SIMPLE_FILE_WORKERS unset).

## Reproduction

Command (canonical source roots per bootstrap-phase4-grouped.shs):

    native-build --target aarch64-unknown-linux-gnu --backend cranelift \
      --runtime-bundle core-c-bootstrap \
      --source src/compositions/cuda_disabled --source src/compositions/kernel_llvm_cranelift \
      --source src/compiler --source src/app --source src/lib \
      --source src/os --source src/plugins --source src/package_ownership --source src/compositions \
      --entry-closure --threads 16 --mode dynload \
      --entry src/app/cli/_CliMain/main_and_help.spl --output build/goal-p4/simple_cli

Result: FAIL. All 4 file-workers exit 1; aggregate `MIR shard aggregate failure;
link and artifact publication blocked`. Receipts: 3, overlap_proven=false.

First error (repeated; all name app.cli._* modules):

    [ERROR] MIR shard error: MIR projected ownership missing HIR for app.cli._CliMain.main_and_help
    error: native-build worker exited with code 1.
    [file-worker] owner=N/4 status=BLOCKED exit=1 claimed=0 sealed=0 finished=false

12 distinct `MIR projected ownership missing HIR for app.cli._*` errors.

## Control

The same command with `SIMPLE_FILE_WORKERS=0` (whole-program in-process lane)
proceeds past parse (3122/3122), surface_build (3122/3122) and into HIR with
zero errors (evidence: build/goal-p4/build3.log in the same worktree). The
defect is therefore specific to the PER-FILE worker-pool lane; the whole-program
lane is unaffected at least through surface freeze.

## Notes

- The whole-program lane had already routed around a related earlier failure:
  with the campaign-scaled shard budgets (SIMPLE_HIR_SHARD_WORKER_KB=9000000 et
  al.) the pool refuses to start (`need >= 30000000 kB free`); default budgets
  are required for the pool to admit workers at all.
- bootstrap_options.md records "Stage 3 run of the per-file lane is not yet
  proven"; this is a full-CLI (phase-4-shape) data point for that gap, at a
  much larger closure than the 9-module proof.

## Status

OPEN. Not fixed in this lane (whole-program lane unblocked the bootstrap goal).
Suggested owner: per-file pipeline (native_file_worker_v1.spl family) —
projected-ownership handshake between HIR claim and MIR claim for app.cli._
modules appears to lose the HIR side under the pool.
