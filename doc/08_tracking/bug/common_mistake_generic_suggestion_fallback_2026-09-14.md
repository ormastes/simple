# 7 of 32 `CommonMistake` variants printed a diagnostic that names no mistake
## Closed 2026-09-16 — Status FIXED 2026-09-14; 7 suggestion arms added, cargo tests pass

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

- Status: FIXED (2026-09-14)
- Binary at discovery: `d4c0779cef6cf0cc4054` (this lane's prior rebuild, already carrying the JavaNew comparison-operator fix)
- Verification binary: rebuilt again in this worktree from this branch's tip, `CARGO_TARGET_DIR=/home/yoon/cargo-unitp1`
- Base: `work/unit-p1-2026-09-13` at `37ea72a6554`
- Area: `src/compiler_rust/parser/src/error_recovery.rs::CommonMistake::suggestion()`

## Found via

The Round-3 cross-directory failure histogram (`scratchpad/unitp1/hist.sh`)
surfaced the compiler's actual printed error text for `object_provider_spec.spl`
(a crash investigated separately — see
`doc/08_tracking/bug/c_backend_export_spec_and_build_targets_spec_triage_2026-09-14.md`
for that thread) repeating: `error: Common mistake detected: See error
message for details`, at ERROR severity, three times in a row before an
abort — a diagnostic that identifies no mistake at all.

## Root cause

The compiler's headline text for a detected mistake is built from
`suggestion()`, not `message()`:

```rust
message: format!("Common mistake detected: {}", mistake.suggestion()),
```

(`parser_helpers.rs:92`, `parser_impl/core.rs:157`). `message()` — the long,
example-bearing text — is exhaustively matched over all 32 `CommonMistake`
variants and always variant-specific. `suggestion()` — the short text actually
shown — was NOT exhaustive: it ended in a wildcard,
`_ => "See error message for details".to_string()`, and 7 of 32 variants had
no explicit arm and fell into it: `RustLifetime`, `RustTurbofish`,
`CppTemplate`, `CppNamespace`, `TsArrowFunction`, `CSemicolon`,
`SemicolonAfterBlock`. Any one of these firing (e.g. `RustTurbofish` for
`Vec::<i64>::new()`, `CppNamespace` for `namespace foo { }`) produced a hard
ERROR-severity compile failure whose only user-visible text was the generic
fallback — strictly worse than a defect report with no message, since it
actively suggests there is more detail elsewhere ("See error message for
details") when there is none.

## Fix

Added the 7 missing arms to `suggestion()`, each matching the existing
one-line imperative style (`"Use 'var' instead of 'let mut'"`, etc.), and
**removed the wildcard arm entirely**, so `suggestion()` is now exhaustively
matched like `message()` already was. This upgrades the previous "someone
might forget to add a case" failure mode into a hard compile error: a future
`CommonMistake` variant added without a `suggestion()` arm will not compile,
rather than silently reproducing this exact defect.

**Regression test**: `error_recovery.rs::tests::test_no_common_mistake_variant_has_the_generic_suggestion`
— enumerates all 32 variants explicitly (mirroring the enum declaration) and
asserts none returns the literal generic string. Belt-and-suspenders with the
exhaustive-match compile guarantee: the test also catches a REGRESSION where
someone maps a real variant to that exact string by hand (which the compiler
alone would not catch). `cargo test --release -p simple-parser --lib
error_recovery`: 8/8 pass (was 7/7 before this change; the new test is
additive, all previously-passing tests still pass unmodified).

## Verified

- `cargo check --release -p simple-parser`: clean (proves the match is now
  exhaustive — this is a compiler-enforced guarantee, not just a test).
- Seed rebuilt (`CARGO_TARGET_DIR=/home/yoon/cargo-unitp1`); not yet
  re-verified end to end against a real spec that previously hit one of the 7
  variants (none of the 3288 tallied failures in the histogram's raw pairs
  were confirmed to be one of these 7 specifically — the histogram's
  generic-message bucket was dominated by `object_provider_spec.spl`, whose
  underlying crash is a separate, host-load-related issue, not necessarily
  one of these 7 variants at all. This fix closes the diagnostic-quality gap
  regardless of which variant was actually firing).

