# check-native-trailing-default-param.shs is RED at origin/main tip (pre-existing)

**Date:** 2026-08-15
**Status:** PARTIALLY FIXED 2026-08-17 — the guard-shape half of this row (silent exit 1 with no verdict line when the binary is absent) is CLOSED: the guard now prints an ERROR verdict and exits 2, and `SIMPLE_BINARY` is injectable. The native-build half is OPEN and is now tracked by `native_trailing_default_param_guard_three_stage_red_2026-08-17.md` (Cause 2).

## Evidence

A/B at identical binary (`bin/release/x86_64-unknown-linux-gnu/simple`, Rust
seed) in fresh detached worktrees:

- pristine `origin/main` (42508ae90fb): exit 1 — `error: native-build worker
  exited with code 1`
- push candidate (42508ae90fb + 7 forward commits, none touching the
  native-build lane): exit 1 — identical output

The failing lane is the guard's `native-build` of its fixture
(`test/fixtures/native_trailing_default_param/main.spl`); the interpreter
pass of the same fixture prints the expected output. Also note the guard
exits 1 SILENTLY when `bin/simple` is absent (gitignored in fresh
worktrees) — it should print an ERROR verdict line instead of nothing.

## Step-over record

Push of range 42508ae90fb..HEAD (coverage-branch reporter, C-runtime compile
fixes, JIT runtime-func docs+vulkan probe, API-vs-IR parity spec, 2 bug-doc
triages) proceeded via the hook's documented override (`git push --no-verify`)
after ALL seven range-bound guards passed (conflict-tree, markers, tree-size,
runtime-api, divergence-delta 16 pre-existing/0 introduced, seed cargo check,
C-runtime 101/101) and this A/B proved the red is pre-existing and untouched
by the range.

## Unblock

Fix the native-build worker failure at origin tip (investigate its truncated
stderr) and make the guard fail-closed with a verdict line when the binary or
build lane is unavailable.

## Re-measured 2026-08-17 (guard-shape lane)

`bin/simple` = the deployed Rust seed built 2026-08-17 12:58 (59,537,240 B).

Guard harness, verbatim last stdout line:

    sh scripts/check/check-native-trailing-default-param.shs --selftest
    PASS — 8 selftest case(s) checked, all verdicts as expected            (exit 0)

    sh scripts/check/check-native-trailing-default-param.shs
    ERROR — nothing was checked: native-build was killed by a signal (exit 255; log saved to /tmp/check-native-trailing-default-param.3996613.log)   (exit 2)

Three things that were previously true are no longer true, all verified in this
checkout:

1. **The silent exit-1 is gone.** The guard emits an ERROR verdict line and
   exit 2 when there is no compiler; `SIMPLE_BINARY` is injectable and selftest
   case 1 (`no-compiler ERROR 2`) covers exactly that. Nothing further is owed
   on the guard-shape half of `native_trailing_default_param_guard_red_at_origin_tip_2026-08-15.md`.
2. **The static-receiver lowering fix is in the tree** — the widened guard
   `static_receiver_name == ""` is present in
   `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`, and the run
   above shows no `undefined variable Widget`.
3. **Cause 3 (the TMPDIR interpolation masking the real error) is fixed** —
   `src/app/cli/native_build_main.spl:235` now hoists `val spill_root =
   env_get("TMPDIR") ?? "/tmp"` out of the interpolation, and the failing run
   above reports its REAL error instead of `function \`TMPDIR\` not found`:

       error: native-build worker timed out after 7200s before producing a binary.

   Also **Cause 1 does not reproduce on this binary**: the 8-line class-method
   repro prints `inline=10` under `SIMPLE_EXECUTION_MODE=interpreter` (it was the
   two stale `/mnt/data/cargo-*` lane seeds that failed).

What is left is **Cause 2 only**: the native-build worker does not finish
compiling a 60-line fixture — 29.4 GB RSS in the earlier measurement, a 7200s
worker timeout in this one. That is a compiler/native-build defect, not a guard
defect, and it is untouched by this lane. The guard is honestly RED (ERROR,
exit 2, fail-closed) and must stay that way until the worker is fixed. Do not
raise `KILL_SIMPLE_MEM_MB`, do not narrow the guard.

## Re-run on rebuilt seed 2026-08-17 (seed md5 669150b61f2f20401a6a895ae54e9fee, 59550432 bytes, mtime 2026-08-17 20:10:45)

    sh scripts/check/check-native-trailing-default-param.shs --selftest
    PASS — 8 selftest case(s) checked, all verdicts as expected        (exit 0)

    sh scripts/check/check-native-trailing-default-param.shs
    ERROR — nothing was checked: native-build was killed by a signal
      (exit 143; log saved to /tmp/check-native-trailing-default-param.667942.log)   (exit 2)

Guard-shape half stays CLOSED (verdict line + exit 2, fail-closed). The
native-build half is unchanged on the new seed: the run was still inside
native-build when the 3000s harness timeout killed it (SIGTERM -> exit 143),
i.e. Cause 2 (native-build worker never finishes the 60-line fixture) does NOT
reproduce as fixed. Status unchanged: PARTIALLY FIXED.
