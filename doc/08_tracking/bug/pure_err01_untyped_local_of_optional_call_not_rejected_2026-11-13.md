# Pure-Simple ERR-01 misses `as` on an untyped local holding an optional call result

Date: 2026-11-13
Status: FIXED (2026-11-13)
Severity: P3
Found by: lane p3-ifval-20261113 (if_val_binding_from_generic_optional_stays_optional_err01_2026-11-13)

## Observed

The self-hosted HIR lowerer's `[E-OPT-CAST-001]` check
(`src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl`, Cast arm)
reads the operand's HIR type or the DECLARED symbol type of a named local /
called function. A local declared without an annotation from an optional
call result has no declared type, so the cast is not rejected:

```simple
fn pick<T>(v: T, ok: bool) -> T?:
    if ok:
        v
    else:
        nil

fn f() -> i64:
    val m = pick(41, true)
    m as i64        # pure-Simple: 0 errors; seed: ERR-01 (correct)
```

Measured 2026-11-13 through `optional_as_cast_rejected_spec.spl`'s
`lowering_errors` helper: `pick(41, true) as i64` -> 1 error (correct),
`val m = pick(41, true); m as i64` -> 0 errors (should be 1).

## Expectation

Parity with the seed: an unannotated `val` initialised from a call whose
declared return type is `T?` carries that optional type into the cast check.

## Resolution (2026-11-13)

Cause: `hir_binding_direct_call_return_kind` (`binding_types.spl`) returns
nil for a generic callee and for an unsettled return (`T?` with a type
parameter, `any?`), so the unannotated local's symbol type stayed nil and the
Cast arm's `cast_operand_declared_type(Ident)` had nothing to read. The direct
`pick(..) as i64` form was caught only because the Cast arm reads the callee's
declared `Function` ret itself.

Fix (diagnostic-only, no type slot changed): `HirLowering.local_optional_call_init`
(`types.spl`), marked by `mark_optional_call_init` (`expression_core.spl`) at all
four val/var lowering sites in `statements.spl` when the binding is unannotated,
not an `if val`/`while val` payload binder (`bind_optional_payload`), its symbol
type stayed unknown, and the initialiser is a direct call whose declared return
is `Optional(_)`. The Cast arm consults it via `cast_operand_is_optional_call_local`.
The table is keyed by module-local SymbolId, so it is cleared in `begin_module`
and `lower_module` (ids restart at 0; found by review — without it a mark leaked
into the next module as a false positive).

Evidence (`test/01_unit/compiler/hir/optional_as_cast_rejected_spec.spl`, seed
with #8883 + #8889): red 5/7 (generic `val` and `var` cases), green 8/8 including
the positives (`if val`, `while val`, `??` initialiser, `??` at the cast,
non-optional call, `unsafe`, `??` shadow rebind) and a two-module no-leak case
(red without the per-module clear).

False-positive check: 14 neighbouring HIR specs (binding/cast/if-val/optional/
unsafe) identical verdicts base vs fixed (two pre-existing failures,
`hir_expr_type_presence_spec` and `binding_subject_owner_retention_spec`, fail
identically on base). Repo-wide scan: of 3,540 tracked `.spl` files with a
numeric `as` cast, 3 have the shape "unannotated local of a same-file
`-> X?` call later cast with `as`". Lowered through the pure-Simple checker:
`if_val_generic_optional_cast_spec.spl` 0 -> 0; `json_ingest.spl` 0 -> 6 and
`free_fn_any_optional_return_spec.spl` 0 -> 1 — both `any?` locals cast after a
`== nil` guard, which the seed ALSO rejects with ERR-01 (verified with a probe;
there is no flow narrowing). These are parity, not false positives.
`src/os/tooling/rust_analyzer_worker/json_ingest.spl` (product code, imported by
`src/app/lint`) was narrowed with `?? 0` (behaviour-identical after the guard).
Single-file lowering cannot resolve cross-module callees, so the scan
under-approximates. After the `?? 0` narrowing the checker reports 0 for `json_ingest.spl`;
its consumers `rust_adapter_spec` 5/5, and `rust_worker_spec` /
`rust_authoritative_session_spec` ERROR executed=0 identically on base.

Remaining: method-call initialisers (`val m = o.get(k)`) and copies of a marked
local (`val n = m`) are still not recognised; the interpreter spec
`free_fn_any_optional_return_spec.spl` still casts an `any?` local (rejected by
both checkers; it runs through the interpreter fallback).
