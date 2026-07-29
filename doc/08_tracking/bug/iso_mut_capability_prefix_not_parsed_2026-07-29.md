# Bug: `iso`/`mut` capability-prefixed types are not parsed by the real frontend (`parse_full_frontend`) at all

- **Date:** 2026-07-29
- **Status:** open
- **Severity:** medium (blocks real-source verification of the capability
  system end-to-end; also hides behind a false-green spec)
- **Found by:** lane ISO1 `iso-real`, while writing a real-source-through-the-
  pipeline spec for iso use-after-move

## The actual defect

`TypeKind.Isolated(Type)` and `TypeKind.Atomic(Type)`
(`src/compiler/10.frontend/parser_types_expr.spl:32-33`) are declared enum
variants, but **nothing in the real recursive-descent parser
(`parse_full_frontend`, the entry point `CompilerDriver`/HIR lowering
actually use) ever constructs them.** Repo-wide grep for
`TypeKind.Isolated(`/`TypeKind.Atomic(` inside `src/compiler/10.frontend/**`
turns up only the two enum-variant declaration lines themselves — zero
construction sites. The parser's parameter/return-type grammar treats a bare
`iso`/`mut` token as an ordinary type NAME, then fails on whatever type
identifier follows it.

Direct repro (via `parse_full_frontend(src, path, path, log)`, the same call
`CompilerDriver.compile()` and
`test/01_unit/compiler/mir/mir_span_thread_spec.spl` use):

```
src = "fn take(a: iso i64) -> i64:\n    a\n"
-> [parser_error] path probe.spl line 1:16: expected ), got Ident 'i64'

src = "fn take(a: mut i64) -> i64:\n    a\n"
-> [parser_error] path probe2.spl line 1:16: expected ), got Ident 'i64'
```

Both `iso` and `mut` fail identically, so this is not iso-specific — the
whole capability-prefix grammar (`mut T` / `iso T` on parameter and return
types, per
`test/03_system/feature/usage/capability_system_spec.spl`'s own docs) is
unimplemented in the real parser.

The only place these AST variants ARE constructed is the treesitter
**outline** parser (`src/compiler/10.frontend/treesitter/outline_types.spl:35`,
`typeoutlinekind_Isolated`) — a separate, lighter-weight pass used for
LSP/docs symbol outlines, not compilation.

## Second finding: `capability_system_spec.spl`'s "40/40 passed" is a false green for its `iso`/`mut` cases

`test/03_system/feature/usage/capability_system_spec.spl` defines `iso`/`mut`
-typed nested functions inside `it` bodies (e.g.
`fn transfer(data: iso i64) -> i64: data`) and asserts only `expect true`
after defining them. It currently reports 40/40 passed
(`bin/simple test test/03_system/feature/usage/capability_system_spec.spl`),
but the direct-repro above proves `parse_full_frontend` cannot parse that
exact syntax. The spec's `it` bodies must be running through the test
runner's own (different, more lenient) interpreter/parsing path, not the
real compiler frontend — so this spec does **not** exercise the real parser
for its `iso`/`mut` cases despite reading as if it does, and would stay
green through a parser regression or through the parser never having
support in the first place (this bug). Flagged separately from the parser
gap itself because it is a testing-integrity issue: `expect true` after a
`fn` definition is not evidence the definition parsed via the pipeline a
real program would use.

## Where

- `src/compiler/10.frontend/parser_types_expr.spl:25-35` — `TypeKind`
  declares `Atomic`/`Isolated` but the surrounding parser file has no
  construction site for either.
- Parameter/return-type parsing (wherever the real grammar builds a
  function's `[Type]` param list — not yet located precisely; the repro
  above localizes the FAILURE but not the exact function name/line, since a
  grep for `fn parse_param`/`parse_fn_param`/`param_list` in
  `src/compiler/10.frontend/*.spl` returns nothing, meaning the parameter
  grammar lives under a name this investigation did not find in the time
  available) never checks for a leading `mut`/`iso` keyword before calling
  the generic type parser.
- `test/03_system/feature/usage/capability_system_spec.spl` — every `iso`/
  `mut` example in this spec (Groups 1, 4, 5, 7-10, 12-13, 15) should be
  re-verified through `parse_full_frontend` once the parser gap is closed;
  right now none of them are meaningful evidence that the grammar works.

## Impact on lane ISO1 (`iso-real`)

This blocked driving real *source text* through the full
`CompilerDriver.compile()` pipeline for the iso use-after-move red-line
probe (the originally planned verification shape). The lane's actual HIR/MIR
changes (`HirTypeKind.Isolated`, the `emit_move` wiring at the
variable-to-variable let-binding site, and the parameter HIR-type threading)
are verified instead with hand-built HIR feeding the real
`MirLowering`/`check_mir_module` pipeline —
`test/01_unit/compiler/borrow/iso_move_pipeline_spec.spl` — mirroring the
same real-parser-gap workaround `mir_span_thread_spec.spl` already
documents for a different pre-existing issue (AST span population). Once
this parser gap is closed, that spec should be extended (or a sibling added)
to drive the same probes through real `iso`/`mut` source text end-to-end.

## Suggested next step

Locate the real parameter-type parsing function (likely under
`src/compiler/10.frontend/parser/` in a file not matched by this
investigation's greps) and add a `mut`/`iso` keyword check before the
generic type parse, constructing `TypeKind.Reference`/`TypeKind.Isolated`
accordingly — mirroring how the existing `HirParam.is_mutable` /
`ReferenceCapability` machinery downstream (monomorphize layer) already
expects to consume a real capability signal from a parsed type.

**Reference implementation already exists in the Rust seed**, a separate
codebase from the pure-Simple parser this bug is about (`.claude/rules`:
"Fix .spl not Rust" — do not port by editing the seed itself, but its
grammar/checking logic is a ready reference to consult):
`src/compiler_rust/compiler/src/hir/capability.rs` (343 lines --
`CapabilityEnv`, aliasing/downgrade rules, `ReferenceCapability` from
`simple_parser::ast`) plus its parser-level tests
`src/compiler_rust/parser/tests/types.rs` and
`src/compiler_rust/driver/tests/capability_{tests,integration_tests}.rs`.
This is very likely *why* `capability_system_spec.spl` reads as green: the
test runner's child process
(`src/compiler_rust/target/debug/simple`, confirmed via
`SIMPLE_COMPILER_TRACE=1` output: `child binary:
.../src/compiler_rust/target/debug/simple`) is the Rust seed binary, whose
native parser already understands `iso`/`mut` -- so a spec `it` body that
literally contains `fn transfer(data: iso i64) -> i64: data` as inline
source parses fine when the *seed's own* engine evaluates the spec file,
independent of whether the pure-Simple `parse_full_frontend` in
`src/compiler/10.frontend/**` (the code path this bug is about, and the one
`CompilerDriver.compile()` uses) supports it.
