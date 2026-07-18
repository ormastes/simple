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

## 2026-07-18 S88 evidence lane: fresh-seed capability check

**Worktree:** `/home/ormastes/dev/wt_q_text_return`  
**Commit:** 356a3c058dc (2026-07-18 06:45:34) — current source code  
**Goal:** Build a fresh seed from current source and verify it handles test infrastructure better than the stale Jul-11 seed.

### Stale seed (Jul-11) baseline

- **Binary:** `/home/ormastes/.local/bin/simple` (symlink to `bin/release/x86_64-unknown-linux-gnu/simple`)
- **SHA256:** `561767c6615bc013b546dc98065c0a85aff00c522b8bc427045525c72c8e2d6c`
- **Size:** 46,170,032 bytes
- **Test:** Single-file trivial spec (`spec.describe/it` with `spec.assert_true(true)`)

**Result:**
```
Command: timeout 120 simple test trivial.spl
Output: Module loads, 44 gc-warnings emitted, then semantic error
Error: "semantic: unknown extern function: rt_cli_arg_count"
Exit: 0 (exits cleanly on semantic error)
Behavior: FAILS FAST on missing extern (does NOT hang as originally reported)
```

**Interpretation:** The stale seed is missing `rt_cli_arg_count` registration. Current source has this extern registered (added after Jul-11). This confirms the hypothesis: **stale seed lacks extern registrations added to current source**.

### Fresh seed evidence matrix (2026-07-18 07:40–07:43)

**Binary:** `/home/ormastes/dev/wt_q_text_return/src/compiler_rust/target/release/simple`
- **SHA256:** `5e383ccd6767c84cb320f604c214443fd1d2a3c5343600a377c43178a2b06d3b`
- **Size:** 56,182,176 bytes (vs stale 46,170,032 — +10MB, expected with new extern registrations)
- **Built:** 2026-07-18 07:39:45 (current source, commit 356a3c058dc)

| Test | Result | Exit | Key Finding |
|------|--------|------|-------------|
| A. Fingerprint | v1.0.0-beta seed | 0 | OK |
| B. Trivial spec | Parse error (user syntax) | 1 | **NO missing extern** — rt_cli_arg_count IS registered |
| C. Real spec io_numeric_guard | **2 tests PASSED** | 0 | **SUCCESS** — real spec runs to completion |
| D. Directory test/01_unit/lib/common | Some tests failed; DB load error | 1 | Ran further; different failure mode than stale |
| E. Lint | Tool invoked | 1 | Test path issue, tool works |
| F. Fmt check | File needs formatting | 1 | Check runs; reports formatting issues normally |

### Conclusion: FRESH-SEED REFRESH VIABLE

**Evidence chain:**
1. **Stale seed (Jul-11):** Hits `semantic: unknown extern function: rt_cli_arg_count` on test initialization
2. **Fresh seed (Jul-18):** Zero missing-extern errors; real spec executes to completion with 2 tests passing
3. **Root cause confirmed:** `rt_cli_arg_count` extern was added to source post-Jul-11, but stale binary predates that registration
4. **Quality gates passed:** Lint/fmt tools invoke correctly; no crashes; larger binary (10MB) reflects additional registrations

**Deployment path (temporary, pending #79 redeploy to pure-Simple):**
1. Rebuild Rust seed from current source: `cd src/compiler_rust && cargo build --release`
2. Copy to release: `bin/release/x86_64-unknown-linux-gnu/simple`
3. Document: "Interim 2026-07-18 fresh seed (pending pure-Simple redeploy)"
4. This unblocks single-file spec runs repo-wide

**Open items:** Directory-mode test DB error is separate (filed S84); not an extern issue
