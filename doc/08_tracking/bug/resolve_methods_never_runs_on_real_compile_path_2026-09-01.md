# `resolve_methods` never runs on the real compile path

**Date:** 2026-09-01
**Status:** OPEN — diagnosed precisely, deliberately NOT fixed (structural)
**Impact:** the root cause of MCP's 120 native-build MIR lowering errors

## Summary

Method resolution is wired only into a bootstrap branch that real builds never
take. Every `MethodCall` therefore reaches MIR lowering carrying the
`MethodResolution.Unresolved` default it was stamped with at HIR-lowering time.

## Gap A — the pass is not called

`src/compiler/80.driver/driver_hir_pipeline_lowering.spl:484` (`lower_and_check_impl`)
branches on `self.ctx.sources.len()`:

- `sources.len() <= 0` -> bootstrap flat-HIR branch, line 547, **calls
  `resolve_methods(hir_module)`**
- `sources.len() > 0` -> the normal multi-source path, line 570 onward — what
  native-build, MCP, and every real multi-file compile use — **never calls it**

The generic wrapper that would call it, `resolve_methods_impl`
(`driver_hir_pipeline_passes.spl:39`), has **zero call sites**:
`grep -rn 'resolve_methods_impl(' src/` returns exactly 1 line, its own
definition. Dead code. (Verified independently by the coordinator.)

`src/compiler/driver/*` mirrors `80.driver/*` byte-identically (`diff`
confirmed), so this is not a path-selection ambiguity between two drivers.

Consequence: the `Unresolved` default stamped at
`20.hir/hir_lowering/_Expressions/expression_core.spl:239,244,250,658,663,668`
survives unconditionally to MIR.

## Gap B — the pass cannot simply be switched on

`HirExpr.type_` is never populated for an ordinary receiver. Every `HirExpr` is
constructed `type_: nil` throughout `20.hir/hir_lowering/**` (dozens of sites),
and **no assignment to `.type_` exists anywhere** under `20.hir/` or `30.types/`
— only a construction-time echo.

`35.semantics/resolve_strategies.spl:26` (`resolve_method`) treats
`receiver.type_ == nil` as an immediate hard error ("receiver type is unknown").

The one place a type does flow is `35.semantics/resolve.spl:483`
(`resolve_call_result_type_raw`), which threads a resolved CALL RESULT type onto
a wrapping `MethodCall` — but only across a chain of already-resolved method
calls, never onto a `Var` read of a previously-declared local.

**So wiring Gap A without fixing Gap B would be strictly worse**: today's silent
`Unresolved`-with-ad-hoc-recovery becomes a loud phase-3 "receiver type is
unknown" for nearly every ordinary-variable method call in the program.

## Why some method calls work today

MIR lowering grew its own independent, receiver-kind-specific type tracking
(`local_is_runtime_array`, `local_mir_type_of`, `struct_value_syms`, `wb_kind`)
purely as a workaround for resolution being structurally absent — documented
in-repo as the "Bug #138/#156 keystone" at
`50.mir/_MirLoweringExpr/method_calls_literals.spl:1489-1500`, and corroborated
by `native_build_filehandle_instance_method_unresolved_2026-08-09.md`.

Whether any given call succeeds depends entirely on whether that fallback
happens to special-case the receiver-kind + method-name pair. That is exactly
why 40 unresolved-method-call, 33 for-in, and 14 enum-match errors coexist with
plenty of working method calls in the same build.

## Corrects a widely-held assumption

MCP's native-build failure was attributed to missing dict iteration (#143).
It is not. With the diagnostics from `7adbf53d618` printing the collection's
MIR type, the 33 for-in errors split:

```
collection mir type: I64     23
collection mir type: Tuple   10
collection mir type: Dict     0     <- not one genuine dict
```

Every for-in error is a collection whose type was already lost — a cascade of
this defect, not a missing feature. Likewise `keys`/`has`/`values` is **not** a
missing dispatch-table row: those methods lower correctly in isolation on a
directly-typed `Dict<text,i64>` local (tested).

## Minimal reproduction

```
fn make_dict() -> Dict<text, i64>:
    var d: Dict<text, i64> = {}
    d["a"] = 1
    d["b"] = 2
    d

fn main():
    val d = make_dict()
    for k in d.keys():
        print k
```

`d` is a `Var` read of a function-returned value — the provenance MIR's local
tracking does not cover and `resolve_call_result_type_raw` does not reach.

NOT executed end-to-end: driving it through `native_build_worker.spl` hit an
unrelated pre-existing blocker (the worker's own closure fails to parse:
`mir_lowering_stmts.spl`, `Unexpected token: expected expression, found
Error("Unterminated f-string")`), and full-closure attempts cost ~18 min each.

## Why this is not being fixed here

A safe fix needs BOTH, together:
1. wiring `resolve_methods` into the normal `sources.len() > 0` path, and
2. plumbing inferred/declared types onto `HirExpr.type_` (or giving
   `resolve_method` an alternate type source) across `Let`/`Var`/`Assign`/
   return-value/match-binding provenance.

That is real compiler engineering spanning `30.types` and `20.hir`, not a
one-line patch, and a wrong type-propagation change produces **silently wrong
values** rather than build errors — the worst failure class in this codebase.
Stopping at diagnosis is deliberate.

## Unix impact

None from this record (documentation only). Note the defect itself is
target-agnostic: it fails identically on Linux and macOS, and is not a Windows
porting gap.

## Corroborating evidence (2026-09-01, MCP session-store slice)

An independent audit of MCP's assistant/session-store files re-measured the full
build at **133 errors** (the earlier 120 undercounted; only 54 carried file
attribution before the diagnostics fixes).

Two findings strengthen this diagnosis:

1. **The unresolved methods are plain stdlib text/array calls with no type
   ambiguity**: , , , , . All are
   confirmed working in the interpreter. If resolution never runs, even a wholly
   unambiguous receiver stays  — which is exactly what is observed.

2. **The class-registration failure cascades ACROSS files.**
   's constructor calls are NOT self-referential — they are
   ordinary calls to types imported from  — yet they fail
   identically because they share MIR module space with the broken
    in . So this is a cross-module
   class-registration-ordering defect, not a per-class quirk.

**Triage warning:** reported error locations are frequently WRONG — several are
attributed to  import lines rather than the real call sites (e.g.
 errors reported at 9:16 while the real usages are at
lines 332/368/407/481/514). Do not trust the location without checking.

**No source fixes were applied to MCP**, deliberately: rewriting idiomatic Simple
to dodge a compiler bug is prohibited by CLAUDE.md and would hide the defect.
