# Agent task plan — unknown decorator/attribute: warning instead of error

**Date:** 2026-11-26
**Lane branch:** `work/unknown-decorator-warn-20261126` (worktree `C:/dev/lanes/decorator-warn`, base `release/1.0.0` @ `44e0bdc201f`)
**Merge owner:** Kimi session; lands via PR to `release/1.0.0`.
**Final reviewer:** coordinating session, zero P0/P1 before merge.

## Motivation

Older compilers hard-fail on decorators they do not know (observed: seed
`error: semantic: unknown decorator @representation_boundary on function ...`
when the tracked seed compiles newer `src/lib`). An unknown tag must degrade to
a warning so newer source stays usable on older toolchains, with an opt-in
strict mode to keep the hard error for CI/qualification.

## Contract (both compilers)

- Unknown `@decorator` (and unknown `#`-attribute if the grammar has one) →
  warning naming the tag and the item; compile continues; no semantic effect.
- `SIMPLE_STRICT_DECORATORS=1` (or an existing warnings-as-errors mechanism,
  wired in addition) restores the hard error.
- Known decorators unchanged. Existing annotation lint
  (`lint_annotation.spl` / `lint/checker_annotations.rs`) untouched.

## Lanes

| Lane | Owns | Status |
|---|---|---|
| S — Rust seed | `src/compiler_rust/**` (error site `compiler/src/decorator_apply.rs:175`) | dispatched |
| P — pure compiler | `src/compiler/**`, `test/**` | dispatched |

## Verify gate

- Seed: `cargo build` + targeted `cargo test`; end-to-end scratch file shows
  warning-by-default and strict-error. Deployed `bin/simple.exe` is NOT
  overwritten; seed rebuild/deploy recorded as follow-up.
- Pure: probe through pure-compiler path; new spec under `test/01_unit/compiler/`
  green on the bootstrap seed (`C:/dev/simple/src/compiler_rust/target/bootstrap/simple.exe`),
  neighboring decorator spec regression-checked.

## Status 2026-11-26 — done

- Seed: `decorator_apply.rs` warns and skips unknown module-level decorators; `SIMPLE_STRICT_DECORATORS=1` restores the hard error. cargo tests 16/16 (3 new). E2E on the interpreter path: default → warning + runs; strict → `error: semantic: unknown decorator ...`.
- Pure compiler: new `10.frontend/core/decorator_check.spl` (known-set grouped by consumer, scope-gated to module-level functions for seed parity, per-(path,line,name) dedup, `parser_warn` + `warning:` print, memoized knob + reset hooks); wired at module-body dispatch arm, module-body fall-through, and nested-decl attributes. `SIMPLE_STRICT_DECORATORS` registered in native-build cache identity; inventory lock updated.
- Specs: `test/01_unit/compiler/frontend/unknown_decorator_warning_spec.spl` 12/12; regressions `parser_inlining_hint_decorators_spec` 3/3, `lint_allow_attribute_spec` 6/6 (release seed `C:/dev/wt-warn-3p1/.../release/simple.exe`).
- Deploy note: tracked `bin/simple.exe` seed picks the fix up at the next seed rebuild/deploy.
