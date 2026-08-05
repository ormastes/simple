# Deployed `bin/simple` is still the Rust seed, not the self-hosted binary

- **ID:** BUG-2026-08-05-deployed-seed-not-selfhosted
- **Date:** 2026-08-05
- **Status:** open, deployment-state only (no source defect)
- **Severity:** medium — contradicts stated policy, hides pure-Simple interpreter
  fixes from `bin/simple run`/`bin/simple test` until redeployed

## Summary

`.claude/rules/bootstrap.md` states: "Default tooling = pure-Simple
self-hosted binary, not the Rust seed... resting state, not an emergency
stopgap." As of this date, `bin/simple` (symlink to
`bin/release/x86_64-unknown-linux-gnu/simple`) still prints:

```
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
```

on every invocation, including `--version`, even though the file's mtime is
current (rebuilt today by some other lane). The binary being fresh does not
make it self-hosted — it is still a seed build.

## Consequence for interpreter-tier fixes

Source changes to `src/compiler/10.frontend/core/interpreter/*.spl` (the
pure-Simple tree-walking interpreter) are NOT executed by the deployed
`bin/simple run` / `bin/simple` bare-positional lanes, because:

- The Rust seed has its own, separate, native interpreter implementation
  (`src/compiler_rust/compiler/src/interpreter_control.rs`) that a program
  actually runs through on the seed — it does not dispatch through the
  `.spl` interpreter source tree.
- `bin/simple test` also hard-defaults to a tree-walk interpreter, but per
  `.claude/rules/testing.md` this is the SEED's own harness, not necessarily
  the pure-Simple `eval.spl` tree either, for ordinary (non-imported-as-library)
  execution.
- The `.spl` interpreter source tree IS reachable from the seed, but only as
  ordinary library code that a test file explicitly imports and calls
  functions from directly (as `test/01_unit/compiler_core/interpreter/match_fallthrough_diagnostic_spec.spl`
  does) — never as "the interpreter that runs subsequent arbitrary source",
  since the seed doesn't use it that way.

Net effect: a fix landed in `eval.spl`/`eval_decls.spl`/`eval_tables.spl` is
verifiable by importing and calling its functions directly from a spec (source
level), but is **not observable** by writing a `.spl` program and running it
through the deployed `bin/simple` today. This affected verification of
BUG-2026-08-01-match-fallthrough's severity-wiring follow-up (`SIMPLE_SAFETY_PROFILE`
promoting the match-fallthrough diagnostic to a hard error) — that wiring is
proven correct at the source/unit level (see
`test/01_unit/compiler_core/interpreter/match_fallthrough_diagnostic_spec.spl`)
but not end-to-end through `bin/simple run`.

## What was checked, not done

- Did not attempt a full bootstrap (explicit repo policy: ad-hoc incremental
  only, escalate only if proven insufficient; also explicit user instruction
  this session).
- Spot-checked existing `.bak` binaries under
  `bin/release/x86_64-unknown-linux-gnu/` for a usable self-hosted build.
  `simple.bootstrap-main-stage-2026-08-01.bak` does NOT print the seed
  warning (banner: `simple-bootstrap 1.0.0-beta`) and may be a genuine
  self-hosted or later-stage build, but its provenance/completeness was not
  verified and it was not promoted to `bin/simple` — that decision needs its
  own verification pass (what stage produced it, whether it has full
  LLVM/JIT/interpreter parity), not a drive-by symlink swap while fixing an
  unrelated feature.

## Suggested next step (not done here)

Verify `simple.bootstrap-main-stage-2026-08-01.bak` (or a fresh T1 incremental
build per `.claude/rules/bootstrap.md`) end-to-end against a small test suite
before considering it for promotion to `bin/simple`.

## Related

- `.claude/rules/bootstrap.md` — stated policy this contradicts
- `doc/08_tracking/bug/match_enum_fallthrough_silent_2026-08-01.md` — the
  feature whose severity-wiring follow-up this gap affects
