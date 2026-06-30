# Warning/Allow Root-Cause Cleanup

## Scope

Repo-wide enforcement cleanup focused on:
- Rust warning gates under `src/compiler_rust/`
- Simple `allow` suppression debt in lint-heavy trees
- CI paths that accidentally downgrade owned failures to advisory output

## Existing Repo Context

- `doc/09_report/fix_allow_suppressions_complete_2026-04-24.md`
  established prior suppression cleanup and should be extended, not replaced.
- `doc/09_report/fix_primitive_api_complete_2026-04-24.md`
  and `doc/09_report/fix_bare_bool_complete_2026-04-24.md`
  already document earlier false-positive reductions for the two largest
  public-API lint families.
- `.github/workflows/rust-tests.yml` still targeted the removed legacy `rust/`
  workspace, so the nominal strict Rust lane was not authoritative on this
  repository layout.
- `rust-tests.yml` already contained `cargo clippy --workspace --all-targets -- -D warnings`,
  but it was unreachable because its directory probe and working directory still
  assumed `rust/`.
- `test/code_quality/allow_suppressions_spec.spl`,
  `test/code_quality/primitive_api_lint_spec.spl`, and
  `test/code_quality/bare_bool_lint_spec.spl` are viable deny-all canaries for a
  targeted Simple strict-lint lane.

## Baseline Captured On 2026-04-30

- `cargo clippy --workspace --all-targets -- -D warnings` from `src/compiler_rust/`
  failed before lint triage completed because:
  - `runtime/src/value/primitive_sort.rs` referenced missing
    `NEON_F64_RADIX_MIN_LEN` and `NEON_I64_RADIX_MIN_LEN` in tests.
  - `runtime/benches/primitive_sort_bench.rs` triggered
    `clippy::unnecessary_sort_by`.
- `bin/simple lint test/code_quality/allow_suppressions_spec.spl test/code_quality/bare_bool_lint_spec.spl --deny-all`
  completed clean, which makes a targeted authoritative Simple lane feasible.

## Root-Cause Findings

1. Enforcement drift was the first failure mode.
   The repo already had strict commands, but the Rust workflow pointed at the
   wrong workspace and therefore could not enforce the intended policy.

2. The current Rust strict baseline still has compile/lint debt outside the
   `allow` tables.
   Fixing the gate requires making the strict command executable first; otherwise
   removing global `allow` entries only hides the real blockers.

3. A targeted Simple lane is safer than a blind whole-tree `--deny-all` sweep.
   Existing code-quality specs provide stable, low-noise canaries that exercise
   the suppression families this cleanup is meant to own.

4. The unknown-annotation family still contains parser/linter whitelist drift.
   Known stdlib decorators such as `@variant`, `@immutable`, and `@no_gc` must
   remain recognized to avoid needless suppression churn.

5. Some existing `unknown_attribute` suppressions are still structurally needed.
   A follow-up spot-check on `src/compiler_rust/lib/std/src/layout/markers.spl`,
   `.../verification/proofs/checker.spl`, `.../mcp/tooling.spl`,
   `.../mcp/mcp_common.spl`, and `.../tooling/compiler/go.spl` showed that the
   current lint path still reports `@extern(...)` usage as `unknown_attribute`.
   Those allows are therefore not stale debt yet; they are evidence of a parser
   or lint classification bug that needs its own fix.

6. Some `unnamed_duplicate_typed_args` allows are now plainly stale.
   The `src/compiler/90.tools/header_gen/` slice no longer needed file-level
   suppressions once a few positional helper calls were converted to named
   arguments.

## Implementation Outcome (DONE — 2026-05-19, commit 461479c0af)

All 5 tasks completed:

- **Task A** — Repaired Rust strict workflow pathing: `.github/workflows/rust-tests.yml`
  now targets `src/compiler_rust/` with the correct Clippy command.
- **Task B** — Added Simple strict-lint workflow: authoritative `--deny-all` lane
  wired to `test/code_quality/` canary specs.
- **Task C** — Fixed primitive-sort runtime/bench compile blockers:
  `NEON_F64_RADIX_MIN_LEN` and `NEON_I64_RADIX_MIN_LEN` constants added;
  `clippy::unnecessary_sort_by` suppression resolved in bench.
- **Task D** — Decorator whitelist alignment: `@variant`, `@immutable`, `@no_gc`
  added to lint recognizer; stale `unnamed_duplicate_typed_args` allows removed
  from `src/compiler/90.tools/header_gen/`.
- **Task E** — Regression canaries added; remaining debt documented (not hidden).

**Allow count:** reduced from 1822 to 1714 (108 suppressions removed).

**Spec tests:** 3 pass — gate wiring (Rust workflow), Simple strict lint, NEON threshold constants.

**Verify:** PASS. 2 known WARNs carried forward as documented debt:
- Lint wrapper segfault (not owned by this feature).
- `@extern` reported as `unknown_attribute` — parser/lint classification bug;
  those `allow` entries are not stale, tracked as follow-up.
