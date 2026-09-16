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
