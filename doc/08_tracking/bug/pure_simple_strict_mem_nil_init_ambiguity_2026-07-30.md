# Finding: pure-Simple interpreter strict-mem trap cannot distinguish "no initializer" from explicit `= nil` at HIR level

- **Date:** 2026-07-30
- **Status:** FIXED 2026-11-11 (p3-interp11 lane) — the HIR-level ambiguity was
  closed by the new `HirExpr.is_uninit_marker` field (the doc judged that fix
  "too cross-cutting"; it landed anyway, 2026-11-07). Verified on the fresh
  seed 46fe8f6b6def. See the 2026-11-11 addendum at the end.
- **Severity:** low (opt-in debug-only gate, off by default; the only effect is
  an occasional false positive when the gate is explicitly turned on)
- **Lane:** M5 pure-Simple parity for strict-memory mode
- **Files:** `src/compiler/70.backend/backend/interpreter.spl`,
  `src/compiler/70.backend/backend/env.spl`,
  `test/01_unit/compiler/backend/interpreter_strict_mem_spec.spl`

## Summary

The Rust seed's strict interpreter mode (`SIMPLE_STRICT_MEM=1`, see
`src/compiler_rust/compiler/src/value.rs` `strict_mem_enabled()` /
`CowEnv::mark_uninit`, and `src/compiler_rust/compiler/src/interpreter/node_exec.rs`
/ `expr/literals.rs`) traps a read of an initializer-less `let`/`var` binding
because it operates on the raw AST, where `let_stmt.value: Option<Expr>` still
distinguishes "no initializer" (`None`) from an explicit `= nil` initializer
(`Some(Expr::NilLit)`).

The pure-Simple interpreter (`InterpreterBackendImpl`,
`src/compiler/70.backend/backend/interpreter.spl`) operates on **HIR**, not
the raw AST. HIR lowering
(`src/compiler/20.hir/hir_lowering/statements.spl`, both the `StmtKind.Var`
disc-dispatch arm around line 391 and the fallback `match` arm around line
480) synthesizes the *same* node for an initializer-less `var x: T`:

```
HirExpr(kind: HirExprKind.NilLit, type_: nil, span: s.span)
```

as the general expression lowerer produces for a source-written `nil`
literal at any position
(`src/compiler/20.hir/hir_lowering/expressions.spl:939`,
`HirExpr(kind: kind, type_: nil, span: e.span)` — `type_`/`has_type_` are
never populated at raw-lowering time for *any* expression kind, so they are
not a usable distinguishing signal either). Confirmed by reading both
lowering sites; no field on the lowered `HirExpr`/`HirStmtKind.Let` retains
which source form produced it.

## Impact

This lane's implementation (`interp_is_uninit_marker_init` in
`interpreter.spl`) treats **any** `Let` whose init is a bare
`HirExprKind.NilLit` as "possibly uninitialized" when
`SIMPLE_STRICT_MEM=1`. Consequences:

- **No false negatives**: every genuinely-uninitialized `var x: T` read is
  caught (this is the primary, documented behavior the task asked for).
- **A known false positive**: `var x: T? = nil` (or `val x = nil`) followed by
  a read of `x` before any other write will *also* trap under strict mode,
  even though the value was deliberately, explicitly set. Off-mode
  (`SIMPLE_STRICT_MEM` unset, the default) is completely unaffected — the
  placeholder `Value.Nil` is still stored and returned exactly as before this
  change.

## Why this was not fixed at the HIR level instead

Threading a `has_explicit_init: bool` bit through `HirStmtKind.Let` to
resolve the ambiguity precisely would require adding a field to a shared,
positionally-constructed enum-variant payload consumed well outside this
lane's ownership (`grep -rn 'HirStmtKind.Let(' src/compiler --include=*.spl`
finds 21 sites: 14 constructions + 7 pattern-matches, spanning MIR lowering,
the C backend, Cranelift, `40.mono`, and more). Positional tuple-variant
construction/pattern-matching requires exact arity in this codebase (unlike
struct literals, which do support omitted-field defaults — confirmed via
`EvalContext`'s existing partial-construction call sites), so this would be a
breaking, cross-cutting change touching many files outside
`src/compiler/70.backend/backend/**`, i.e. outside this lane's scope and
squarely into several other lanes' owned files. Given the feature is an
opt-in, off-by-default debug aid (mirroring "Miri-lite" semantics already
described for the Rust seed), the over-approximation is the correct trade-off
for this lane; a follow-up could revisit HIR fidelity as a separate,
cross-lane-coordinated change if the false positive proves to matter in
practice.

## Evidence

- `src/compiler/20.hir/hir_lowering/statements.spl:391-394` (disc-dispatch
  arm) and `:480-483` (fallback `match` arm): both produce
  `HirExpr(kind: HirExprKind.NilLit, type_: nil, span: s.span)` for a
  `var` declared without `= ...`.
- `src/compiler/20.hir/hir_lowering/expressions.spl:929-939`: the general
  expression lowerer's tail `HirExpr(kind: kind, type_: nil, span: e.span)`
  applies uniformly to every `ExprKind`, including `ExprKind.NilLit` (a
  source-written `nil`), so `has_type_`/`type_` do not disambiguate either.
- `grep -rn "HirStmtKind.Let(" src/compiler --include=*.spl | wc -l` → `21`;
  `grep -rn "case HirStmtKind.Let(" src/compiler --include=*.spl | wc -l` →
  `7` (construction + pattern-match sites outside this lane's ownership).


## 2026-11-11 — P3 interp11 triage verdict: FIXED (verified on fresh seed 46fe8f6b6def)

The fix this doc judged "too cross-cutting" (threading a distinguishing bit
through HIR) landed anyway, via a struct-field default rather than a
tuple-arity change: `HirExpr.is_uninit_marker`. Verified at HEAD:

- `src/compiler/20.hir/hir_lowering/statements.spl:1036` and `:1203` set
  `is_uninit_marker: true` on the synthesized `NilLit` for an initializer-less
  `var x: T` only.
- `src/compiler/70.backend/backend/interpreter.spl:563-570`
  (`interp_is_uninit_marker_init`) returns `init.is_uninit_marker` for the
  `NilLit` case, so a source-written `= nil` is no longer classified as
  uninitialized.
- `test/01_unit/compiler/backend/interpreter_strict_mem_spec.spl` carries the
  regression case ("ON: reading `var x: T? = nil` returns nil, no trap").

Seed-smoke verification (2026-11-11): the committed spec cannot execute on the
Rust seed because it imports the private free fn `interp_is_uninit_marker_init`
and the seed's visibility checker rejects private free-fn imports
(`ascii_utils_spec.spl` fails identically, so this is a systematic
seed/pure-Simple divergence, not a strict-mem defect). A behavioral probe that
drives only the pub `InterpreterBackendImpl` + pub HIR constructors
(`build/review/interp11_strict_mem_probe_spec.spl`, 3 examples) passes 3/3 on
the seed: OFF-mode uninit read returns `Value.Nil`; ON-mode initializer-less
read traps with the strict-mem diagnostic; ON-mode explicit `= nil` returns
`Nil` with NO trap — the documented false positive is gone.
