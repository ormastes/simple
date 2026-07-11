# Stage4 redeploy blocker — seed `llvm-lib` method-call arity + extern-signature codegen bug (2026-07-06)

**Context:** the ~130 source fixes on `main` are frozen behind a redeploy (a fresh
self-hosted compiler build). This doc characterizes why the **seed `llvm-lib`** path
fails, so it can be fixed. (The seed `cranelift` path is separately blocked by the
ANY-erased `Dict<text,Value>` wall — see `doc/03_plan/cert/redeploy_selfhost_plan.md`.)

## What was tried
`src/compiler_rust/target/bootstrap/simple native-build --backend llvm-lib --entry
src/app/cli/main.spl --source src/compiler --source src/app --source src/lib
--entry-closure -o <out>` (full CLI, the real redeploy target). Also
`scripts/bootstrap/bootstrap-from-scratch.sh --pure-simple` (its stage-4 drives the
same seed+llvm-lib on `main.spl`).

## Result: FAIL (rc=1) — LLVM IR verification errors, two classes
- **545 × "Incorrect number of arguments passed to called function"** — on METHOD
  calls lowered as `%mcall_direct = call ... @<Module>__<Type>.<method>(i64 a, i64 b)`.
  The generated call passes the wrong number of i64 args vs the callee's LLVM
  signature. Named examples: `str.substring`, `CompilerContextImpl.check_types`,
  `VhdlConstraintChecker.sanitize_clock_domain_name`. The volume (545) across many
  modules points to **one root cause**: the seed's `llvm-lib` method-call lowering
  mis-counts the receiver/`self` param (or double-counts it) for direct method calls.
- **25 × "Call parameter type does not match function signature"** — on extern calls,
  esp. `%call = call i8 @rt_dir_create(i64, i64)` where the runtime declaration and
  the call site disagree on arg types/count. An extern-signature registration mismatch.

## Bootstrap-path corroboration
`bootstrap --pure-simple`: **stage2 native-build failed (exit 1) "empty MIR bodies"**
(`bootstrap_stage2_empty_mir_bodies_2026-07-05.md`); stage3 produced no executable;
stage4 fell back to the seed → same llvm-lib errors. No fresh binary produced (only a
stale `build/bootstrap/full/simple` from Jun 28 exists).

## Why this matters / next attack
Redeploy needs a working seed backend. Both fail:
- `cranelift`: ANY-channel `Dict<text,Value>`/enum-payload wall.
- `llvm-lib`: the method-arity bug above (545×, likely one fix) + extern-signature (25×).
The `llvm-lib` method-arity bug is the **more tractable** lead — a single fix in the seed's
llvm-lib direct-method-call lowering (self-param counting) could clear the bulk. Fix
locus: `src/compiler_rust/compiler/src/codegen/` (the llvm-lib method-call emit path) +
the extern signature registration for `rt_dir_create`.

## Also: raw deployed `bin/simple native-build --entry main.spl`
Hits a frozen MIR-empty bug ("MIR module has no functions" for the entry) — not a viable
redeploy path on the deployed binary. So redeploy cannot bootstrap through the deployed
binary either; it must go through a fixed seed backend.

## Minimal single-file repro (2026-07-11, RV64 `--backend llvm` — same bug class)
The plain `llvm` backend hits the identical arity failure on ONE small file, making this
a much cheaper debug target than the 545-error full-CLI run:

- File: `src/os/services/database/simple_db_service.spl` — a class whose read-only
  methods were declared `fn` (not `me`) and called via `self.`:
  `self.has_table(t)` → `call i64 @...SimpleDbService.has_table(i64, i64)` fails LLVM
  verification with "Incorrect number of arguments passed to called function!"
  (same for `has_key`, 3 args). Pattern: the call site passes `self` but the emitted
  callee signature for a non-`me` `fn` class method does not include it (or vice versa).
- Command (fails deterministically with a clean cache):
  `rm -rf .simple/native_cache && src/compiler_rust/target/release/simple native-build --source build/os/generated --source src --source examples --backend llvm --opt-level=aggressive --log on --entry-closure --entry src/os/kernel/arch/riscv64/boot.spl --target riscv64-unknown-none -o build/os/simpleos_riscv64.elf --linker-script src/os/kernel/arch/riscv64/linker.ld`
- Source-side workaround (applied 2026-07-11): declare those methods `me`; the fresh
  build then completes `51 compiled, 0 cached, 0 failed`.
- NOTE: with a warm cache this failure is MASKED — the file is "skipped (non-critical)"
  and a stale cached object links instead. See
  `native_build_noncritical_skip_stale_cache_masking_2026-07-11.md`.
