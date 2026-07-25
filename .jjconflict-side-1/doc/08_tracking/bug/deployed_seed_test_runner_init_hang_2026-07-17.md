# Deployed release binary: single-file `simple test` hangs on ALL specs (stale Jul-11 seed)

**Date:** 2026-07-17
**Severity:** high (blocks single-file spec runs repo-wide on the deployed binary)
**Status:** OPEN — hypothesis pending fresh-seed confirmation

## 2026-07-18 native-owner update

The separate self-hosted native gap is now fixed in source: hosted C owns
`rt_process_run_bounded` on POSIX and Windows, the pure-Simple LLVM backend
routes it through `rt_process_run_bounded_tuple`, and strict Stage4 admits the
exact process-provider symbol. This does not refresh the deployed Rust seed;
the artifact-skew symptom in this report remains open until a current
pure-Simple tool is deployed.

## Symptoms

At origin tip 99f0294dbda, using the deployed release binary
`bin/release/x86_64-unknown-linux-gnu/simple`:

1. **Single-file spec runs hang universally.** `timeout N bin/simple test <any-spec>.spl`
   → rc=124, for every spec tried — including a vanilla `describe/it` spec with
   zero `use` statements. Last output before the wedge is the module-load
   gc-warning for `std.nogc_sync_mut.test_runner.test_executor_composite_jit_generic`;
   zero additional output between the 90s and 240s marks (true indefinite spin,
   not slowness).
2. **Directory-mode gets further, then breaks differently.**
   `bin/simple test test/01_unit/lib/common` loads, discovers 715 tests, starts
   running, then errors `semantic: unknown extern function: rt_process_run_bounded`
   and hangs. `rt_process_run_bounded` IS registered in current-tree seed source
   (`src/compiler_rust/compiler/src/interpreter_extern/mod.rs`) — the deployed
   binary predates the registration.
3. **`bin/simple run` is unaffected**: files importing `app.io.mod` or
   `compiler.core.interpreter.module_loader_core` load and run clean (rc=0).

## Binary identity (key fact)

The deployed release binary is a **Rust seed**, not the self-hosted binary:
it prints "WARNING: this Rust-built Simple binary is a bootstrap seed only".
Fingerprint: 46,170,032 bytes, mtime 2026-07-11 08:52, sha256 prefix
`561767c6615bc013` (unchanged since Jul 11). The pure-Simple self-hosted
redeploy has been walled since bug #79; the release path holds this stale seed
as a stopgap, so `simple test` currently runs on a 6-day-old seed interpreting
current-source .spl infra.

## Hypothesis

Matches the release-sanity finding "Jul-16 seed stage1 spin = seed-binary
regression (fresh seed clean)": the stale Jul-11 seed binary regresses against
current-source .spl (test-runner init spin + missing extern registrations).
Confirmation test: build a fresh seed from current source and run the
vanilla-spec probe on it — if clean, the fix is refreshing the seed at the
release path (interim) and, properly, landing the stage-2 redeploy unblock
(LLVM method-call→rt_* lowering, see
`doc/08_tracking/bug/seed_stage2_llvm_method_symbol_lowering_2026-07-17.md`
lane S63) so the true self-hosted binary can be redeployed.

## Non-causes (ruled out 2026-07-17)

- app.io.mod import cycle — refuted; see the refutation section in
  `S61_interpreter_stack_overflow_app_io_mod_2026-07-17.md`.
- Test-runner infra importing the suspect modules — repo-wide grep negative.
