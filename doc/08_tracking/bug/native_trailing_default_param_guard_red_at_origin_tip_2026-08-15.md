# check-native-trailing-default-param.shs is RED at origin/main tip (pre-existing)

**Date:** 2026-08-15
**Status:** OPEN — guard red, cause environmental/native-build lane

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
