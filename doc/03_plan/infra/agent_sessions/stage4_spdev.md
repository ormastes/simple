# Lane: Stage 4 / `$sp_dev`

Goal: complete the pure-Simple x86_64 Stage 4 bootstrap, verify the exact fresh
CLI, and deploy it only after the bounded essential-tools smoke passes.

## Current state (2026-08-02)

- Stage 3 incremental refresh passes and normally reuses 724/727 cached units.
- Stage 4 reaches HIR lowering without the former `vulkan_backend.spl` parser
  ambiguity or phase-3 segmentation fault.
- The native `Dict.len() == -1` compatibility bug is handled by counting typed
  HIR dictionary keys.
- Fatal HIR errors stop before failed-module retention, preventing the former
  20-minute / 15.8-GiB post-HIR runaway.
- The latest three-cycle session ended on unresolved `print_raw` in
  `src/app/io/_CliCommands/run_commands.spl`. The concrete-owner repair is
  pushed as `4bc9e987ea3a`; it has not yet received a fresh Stage 4 run.
- The Sol-high retained-surface optimization is pushed as `545a6c297248` and
  likewise awaits Stage 4 measurement.
- No fresh Stage 4 CLI has passed sanity or the essential-tools smoke, and no
  artifact has been deployed.

## Required next run

1. Fetch/rebase current `main` and preserve the existing Stage 3/native cache.
2. Refresh Stage 3 incrementally because compiler sources changed.
3. Run one full-resource Stage 4 cycle with the progress/RSS watcher.
4. On a distinct failure, claim it in the bug DB, fix pure-Simple first, add
   exact and adjacent regression coverage, push, and retry within the
   three-cycle session cap.
5. On success, run sanity and
   `scripts/check/check-bootstrap-essential-tools-smoke.shs` against the exact
   fresh Stage 4 binary. Require test-runner, lint, duplicate-check, and
   aggregate PASS markers.
6. Deploy only that verified binary, record its path and hash, and update this
   document with the retained logs and evidence.

## Performance evidence

- Stage 4 remains effectively single-core during frontend/HIR work.
- Recent fail-fast runs reach about 6.5--6.8 GiB RSS at 150 seconds.
- Whole-compiler cache identity can force 727/0 rebuilds; relaxing it remains
  unsafe until canonical complete MIR fingerprints and ordered direct
  dependency-interface hashes exist.
- Accepted optimizations remove redundant path canonicalization, deduplicate
  physical Phase-1 queue work, skip irrelevant facade-hint splits, and compact
  proven-unused retained implementation metadata.

## Ownership

The parallel lane split, merge owner, and final reviewer are recorded in
`doc/03_plan/agent_tasks/stage4_spdev.md`.
