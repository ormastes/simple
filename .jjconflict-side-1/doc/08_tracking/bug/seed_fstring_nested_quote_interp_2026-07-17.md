# Seed f-string lexer REGRESSION: nested string literal inside interpolation breaks (2026-07-17)

**Found by:** release sanity, stage1 retry with freshly built seed
(`src/compiler_rust/target/bootstrap/simple`).

## Status: regression, not a longstanding gap (A/B proven)

Probe `print("j={xs.join("-")}")` with `xs = ["a", "b"]`:

- Jul 11 deployed seed (`bin/release/x86_64-unknown-linux-gnu/simple`):
  prints `j=a-b` — CORRECT.
- Fresh seed built 2026-07-17 from current `src/compiler_rust`:
  prints `-35948` — **silent miscompile** (no diagnostic at all).

So a recent Rust-source change broke quote tracking inside `{...}`
interpolation. Depending on surrounding tokens it surfaces three ways:

1. silent wrong output (probe above) — the dangerous one;
2. `expected Comma, found FString([Literal(")}"), Expr("value_tok")])`
   (parser_preprocessor.spl:207 shape);
3. `Unexpected token: expected Colon, found RBrace`
   (spirv_builder.spl:234: `"struct_{member_ids.map("{_}").join("_")}"` —
   nested literal itself containing an interpolation).

~91 nested-quote-in-interpolation sites exist across `src/app` + `src/compiler`
(grep sweep), so this breaks Stage 1 bootstrap and can silently corrupt any
build that gets past parsing. Fix the seed lexer; do NOT mass-rewrite `.spl`
sources (two sites were temporarily hoisted during diagnosis —
parser_preprocessor.spl, c_type_mapper.spl — revert once the lexer fix lands).

## Misdiagnosis corrected

Empty dict literal `{}` in constructor named-arg position is FINE (probe
compiles and runs); the spirv_builder failure was shape 3 above, not the `{}`
at lines 60-61. The seed also reports f-string parse errors without
line numbers, which cost real time — diagnostics gap worth fixing alongside.

## Related

- `bootstrap_stage1_entry_closure_spin_oom_2026-07-17.md` — separate Jul 16
  prebuilt-seed spin (fresh seed does NOT spin); both block stage1.

## Status (2026-07-18)

FIXED+PUSHED at 310bcdf1131 (strings.rs lexer fix) + 7a27c446582 (.spl hoists revert). Regression tests: 25/25 + 19/19 + 4/4 passed.

Self-host follow-up (2026-07-18): a Stage-2 binary linked against a stale
`libsimple_native_all.a` reproduced the old comma-in-interpolation parse error
even though the freshly rebuilt seed accepted it. Rebuilding that companion
archive cleared the parser failure. The existing expression test now includes
the exact `types.join(", ")` form so future parser-bearing artifacts cover the
observed syntax, not only single-character separators.
