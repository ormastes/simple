# CPU SIMD Direct Fill Full Bootstrap Stage 4 Spin

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

Date: 2026-07-08

## Status

Mitigated; full deploy still unproven.

## Context

`rt_engine2d_simd_fill_u32` is registered in the Rust interpreter extern table
and the Simple SIMD fill path now calls it with scalar fallback. Retained
4K/8K performance evidence still needs a pure-Simple deployed binary before the
direct-fill path can be measured without using the Rust seed.

## Reproduction

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy
```

Observed on `x86_64-unknown-linux-gnu`:

- Rust seed/runtime rebuild completed.
- Stage 2 produced `build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple`.
- Stage 3 reported no self-host executable and fell back to seed for stage 4.
- Stage 4 ran:
  `src/compiler_rust/target/bootstrap/simple run src/app/cli/native_build_main.spl -- --backend cranelift --source src/compiler --source src/app --source src/lib --entry-closure --threads 16 --cache-dir build/bootstrap/native_cache --mode dynload --entry src/app/cli/main.spl --runtime-path ... -o build/bootstrap/full/x86_64-unknown-linux-gnu/simple`
- The worker stayed CPU-bound for about 22 minutes before manual termination.
- `build/bootstrap/native_cache` contained only `bootstrap-wide-inputs.sha256`;
  no object output or full CLI executable was produced.

## Impact

The direct in-place SIMD fill path cannot yet be validated with retained
pure-Simple 4K/8K performance evidence from this workspace. Rust-seed tests can
prove the extern registration and source path, but retained performance reports
must wait for a successful pure-Simple deploy.

## Mitigation

Entry-closure discovery now deduplicates at enqueue time in both native-build
closure walkers:

- Simple `native_build_main.spl` uses dictionaries for discovered files and
  import-resolution cache entries instead of linear scans.
- Rust native-project discovery tracks queued files separately from processed
  files, so fan-in imports cannot enqueue the same dependency repeatedly before
  first visit.

Focused evidence:

- `cargo test -p simple-compiler --lib test_entry_closure_handles_shared_import_fan_in`
  passed.
- The updated Simple source contract for entry-closure traversal passed under
  the bootstrap seed. The surrounding spec still has unrelated stale failures.

## Next Step

Rebuild/deploy a pure-Simple `bin/simple` and rerun the retained 4K/8K SIMD
performance evidence. Keep `build/bootstrap/native_cache` and use isolated mini
caches for any further bootstrap probes.

## 2026-08-17 re-verification — BLOCKED (bootstrap forbidden) + one STALE attribution

A full bootstrap (`scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap
--deploy`) is the only stated reproduction, and running one was **forbidden this
session** — a live bootstrap owned the host at ~98% CPU and was the user's top
priority. The Stage 4 spin was therefore NOT re-attempted, and no claim is made
about whether it still occurs.

**Stale attribution, corrected.** The "Mitigation" section credits:

> Simple `native_build_main.spl` uses dictionaries for discovered files and
> import-resolution cache entries instead of linear scans.

That code is **not in `src/app/cli/native_build_main.spl`** at tip, and cannot
be: the file is a 390-line argv wrapper that spawns
`src/app/cli/native_build_worker.spl` as a subprocess and contains no closure
walker, no dictionary of discovered files, and no import-resolution cache. A
tree scan for entry-closure logic
(`/usr/bin/grep -rln "entry_closure\|entry-closure" src/app src/compiler/80.driver`)
does not list `native_build_main.spl` at all; the pure-Simple closure walkers now
live in `src/app/io/_CliCompile/compile_targets.spl`,
`src/app/cli/bootstrap_focused_native_build.spl`, and
`src/compiler/80.driver/driver_source_*loading.spl`. Anyone re-checking this
mitigation must look there, not here. The Rust half of the mitigation
(`native-project` discovery tracking queued vs processed files) is under
`pipeline/native_project/**`, owned by another lane.

The remaining substance of this bug — "rebuild/deploy a pure-Simple `bin/simple`
and rerun the retained 4K/8K SIMD performance evidence" — is by construction a
bootstrap+deploy task and stays open.

### What could NOT be proven this session
- Whether Stage 4 still spins CPU-bound without emitting objects.
- Whether `build/bootstrap/native_cache` still ends up holding only
  `bootstrap-wide-inputs.sha256`. `build/bootstrap/**` was off-limits.
- Any 4K/8K SIMD performance number, and whether `rt_engine2d_simd_fill_u32` is
  reached on a pure-Simple binary — no pure-Simple binary was built or deployed.
- The `cargo test ... test_entry_closure_handles_shared_import_fan_in` evidence
  line was not re-run.
