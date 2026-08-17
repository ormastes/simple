# Bug: `iso`/`mut` capability-prefixed types are not parsed by the real frontend (`parse_full_frontend`) at all

- **Date:** 2026-07-29
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  `mut T` capability-prefix parsing is also handled now; HIR-side consumption of the
  `mut`/exclusive side-table was not re-audited in this pass (out of scope: this bug is
  titled around the *parser* gap, which is closed).
- **Severity:** medium (blocks real-source verification of the capability
  system end-to-end; also hides behind a false-green spec)
- **Found by:** lane ISO1 `iso-real`, while writing a real-source-through-the-
  pipeline spec for iso use-after-move

## Re-verification (2026-08-07)

Re-checked empirically against current `src/compiler/**` (not by re-reading this
doc or old memory). The parser gap described below **no longer exists**:

- `src/compiler/10.frontend/core/parser.spl:565-571` — `parser_parse_type_impl`
  (the function that underlies `parser_parse_type()` /
  `parser_parse_type_with_union()`, called 9x across the frontend) now has an
  explicit branch: `if kind == 6 and par_text_get() == "iso":` that registers
  the inner type via `isolated_type_register(...)` and returns a
  `TYPE_ISOLATED_BASE`-tagged id, dated "LANE ISO2 (2026-07-29)" in the
  surrounding comment — landed same day as this bug, after the original filing.
  A parallel `mut T` branch exists at lines 540-549 (`exclusive_type_register`).
- Call-graph trace confirms this is the REAL path, not a side parser:
  `fn take(a: iso i64) -> i64: a` (regular `fn` decl) parses its param type via
  `parser_decls_fn.spl:138 parser_parse_type_with_union()` →
  `parser.spl:950 parser_parse_type_with_union()` → `parser.spl:461
  parser_parse_type()` → `parser.spl:477 parser_parse_type_impl()` — i.e. the
  exact function/line sequence the original repro (`fn take(a: iso i64) -> i64`
  → `expected ), got Ident 'i64'`) went through.
  `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl:402-410` rebuilds
  the real `TypeKind.Isolated(inner)` from the flat tag
  (`TYPE_ISOLATED_BASE + id`), so construction sites are no longer "zero" as
  originally reported — they now include `parser_types_expr.spl:178,181`
  (discriminant probes) and `convert_nodes.spl:410,451` (Isolated/Atomic
  rebuild).
- `emit_move` (`src/compiler/50.mir/mir_data.spl:353`) went from the
  documented single call site to **8 call sites** across
  `mir_lowering_stmts.spl` (5) and `_MirLoweringExpr/switch_operators_calls.spl`
  (1, for call-argument moves) plus 2 more in `mir_lowering_stmts.spl` for
  field/dict/array moves — the "starved of facts" gap from the original
  finding #2 is substantially closed.
- The struct-binding TODO (original finding #3, `mir_lowering_stmts.spl:664-672`,
  "iso-typed struct bindings emit copy not move") is also addressed: current
  `mir_lowering_stmts.spl:786-793` has a `struct_is_place_iso` branch that calls
  `emit_move` instead of `maybe_copy_struct_value` for exactly that case, with a
  "WP-E parity: an iso struct is exactly the shape of a resource handle" comment.
- `function_lowering.spl:209,270,770` show `HirTypeKind.Isolated` is consumed at
  the parameter-lowering level too, not just the let-binding level documented
  originally.
- Smoke-tested via `bin/simple check` on `fn take(a: iso i64) -> i64: a; fn
  main(): println(take(5))` — parses and typechecks clean (no "expected )"
  error). **Caveat:** the currently-deployed `bin/simple` (and
  `bootstrap/stage3/x86_64-unknown-linux-gnu/simple`, identical BuildID) is the
  Rust seed, not the pure-Simple self-hosted binary — this is the SAME
  measurement trap this bug doc already flagged (seed's native parser
  understands `iso` regardless of `src/compiler/10.frontend/**` state), so this
  smoke test does **not** independently confirm the fix. The fix claim above
  rests on the source/call-graph trace, not on the binary run. No bootstrap
  rebuild was performed (out of scope for this task) to produce a pure-Simple
  binary for a binary-level re-confirmation — that remains a follow-up if
  independent binary-level proof is wanted.

Net: the specific defect this bug reports (parser cannot parse `iso T` /
`mut T` in parameter position) is fixed in current source. What was NOT
re-verified in this pass: (a) whether `capability_system_spec.spl` and
`iso_move_pipeline_spec.spl` have been updated to drive real source text
through `parse_full_frontend` per the "Suggested next step" below (still
open as a follow-up), and (b) end-to-end use-after-move diagnostics on real
`iso` source through a genuine pure-Simple-compiled binary (blocked by the
seed-vs-self-hosted binary gap above, not by this bug).

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
