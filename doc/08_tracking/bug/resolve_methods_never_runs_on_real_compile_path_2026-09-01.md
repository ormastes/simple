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

## Fix scoping (2026-09-01, second session)

Scoped as directed: what a correct fix requires, with the subset that was
already computed-and-discarded plumbed behind `SIMPLE_RESOLVE_METHODS=1`
(default OFF, landed `260a923ad3b` + follow-up).

### 1. Provenance table — where `HirExpr.type_` could come from

| provenance | type available at HIR construction? | where | status |
|---|---|---|---|
| `val`/`var` with declared type | YES — lowered and stored on the `Let` stmt AND in `Symbol.type_` (`statements.spl:390-401` `symbols.define(...)`) | `20.hir/hir_lowering/statements.spl` | already stored, never consulted by resolution — now consulted (quiet mode) |
| function parameters + `self` | YES — `define(p_name, SymbolKind.Parameter, p_type, ...)` (`_Items/declaration_lowering.spl:119,350`) | symbol table | already stored — now consulted via `infer_symbol_value_type` |
| `Var` read | derivable — `symbols.get_symbol_raw(sym).type_` | resolver | `infer_expr_type` Var arm (pre-existing, was dead) |
| `Let` with inferred type from a call | derivable — callee's symbol type is `Function(params, ret, ...)`: same-module fns predeclared with `declared_callable_type` (`module_declarations_bootstrap.spl:139`), IMPORTED fns too (`module_import_registration.spl:512`, `declared_imported_surface_callable_type`) | resolver | now recorded per-function in `local_value_types` (quiet mode); placeholder `Infer` returns filtered out |
| method-call chain result | YES within a resolved chain — `resolve_call_result_type_raw` (`resolve.spl:483` call site) | resolver | pre-existing; only fires once resolution succeeds |
| `StructLit` / `EnumLit` | YES — the lit carries `type_` | `infer_expr_type` StructLit arm | pre-existing |
| `Index` on typed base | derivable (Array/Slice/Dict element) | `infer_expr_type` Index arm | pre-existing |
| field access (`a.b.method()`) | NOT covered — `infer_expr_type` has NO `Field` arm; needs struct-def field-type lookup | gap | listed, not extended |
| match bindings | NOT covered — no binding registration in resolver | gap | listed, not extended |
| tuple-index / assignment-flow / narrowing | NOT covered | gap | listed, not extended |
| constants | YES — `HirConst.type_` | resolve_module | pre-existing |

99 `type_: nil` construction sites exist under `20.hir/hir_lowering/**`; they
do NOT each need fixing — the resolver-side attach (below) types receivers at
resolution time from the symbol table + binding env, which is the contained
alternative to touching construction sites.

### 2. Does `30.types` already compute what is needed? — TWO-TIER verdict

**Full HM inference: NO, not "computed and merely discarded" — it is not even
run.** `run_typecheck_warn_pass` (`driver_hir_pipeline_passes.spl:175`) is the
only real-path caller of `HmInferContext.infer_module`, and it is gated at
`driver_hir_pipeline_lowering.spl:1023` on `SIMPLE_TYPECHECK_WARN=1` or a
non-Advisory profile — the DEFAULT is Advisory, so the pass does not execute
at all on a default build. When it does run it returns diagnostics only; the
per-expression types live in its internal `Substitution` and die with it.
Writing them back is not plumbing: `HirExpr` has NO node id (fields: `kind`,
`has_type_`, `type_`, `span` — `hir_definitions.spl:533`), so a side table
keyed by expression identity is impossible; writeback means a rebuilding
traversal of every function body.

**Declared/structural types: YES — computed, stored, and never consulted.**
Three pieces were already built and dead:
- `Symbol.type_` populated for params, `self`, annotated locals, constants,
  same-module fns AND imported fns (full `Function` signatures) — nothing on
  the resolution path ever read it for a receiver.
- `MethodResolver.attach_inferred_type` + `infer_expr_type` +
  `infer_symbol_value_type` (`resolve_lookup_helpers.spl:25-71`):
  a complete structural typing helper covering Var/NamedVar/Call/StructLit/
  Index — with **zero call sites** (grep: only its definition and the
  `__init__.spl` re-export). Same shape as `resolve_methods_impl`: built,
  exported, wired to nothing.

So step 5's condition held for the subset, and the plumbing was attempted.

### 3. What was landed (env-gated, default OFF)

`SIMPLE_RESOLVE_METHODS=1` runs `run_resolve_methods_quiet_gated`
(`driver_hir_pipeline_passes.spl`) from `compile()` orchestration AFTER phase
3 — deliberately after both the streaming and non-streaming lowering branches
converge (`driver_orchestration.spl`, after "phase 3 done"), and after every
`hir_cache` store/load, so the HIR cache carries unresolved modules on both
flag settings and cannot be poisoned by the flag.

Quiet mode (`MethodResolver.quiet`, `resolve_methods_quiet`):
- `add_error` is a no-op — resolution failure degrades to exactly today's
  `Unresolved`, making the experiment MONOTONE: a call either becomes
  genuinely resolved or reaches MIR unchanged. This also absorbs the builtin
  problem: `Dict`/`[T]`/`text` receivers have no type symbol
  (`get_type_symbol` returns nil), so all three strategies legitimately miss
  — in loud mode that would have been an error per call.
- receivers get `attach_inferred_type` before `resolve_method`, and the TYPED
  receiver is stored in the rebuilt `MethodCall`, so MIR's type-directed
  fallbacks (`maybe_receiver_type_for_call`, `receiver_is_dict`, etc.) see
  the type even when resolution stays Unresolved — this is where the for-in
  cascade wins are expected, independent of resolution proper.
- unannotated `Let`s are backfilled into a per-function
  `local_value_types: Dict<i64, HirType>` consulted ahead of the symbol
  table; `Error`/`Infer` placeholders are refused at both the backfill and
  the attach (a stamped `Infer` would pass the nil guard while carrying no
  dispatch identity).

Two latent defects found and fixed on the way:
- `create_trait_solver_for_resolution` (`resolve.spl`) partially constructed
  `TraitSolver` WITHOUT `trait_methods` — nil field, crashing
  `try_trait_method_with_solver` the first time a typed receiver reached it.
  It never fired before precisely because the pass never ran with types.
- (spec-harness observation) a symbol-table `Function` type can carry an
  `Infer` return on the direct-lowering path; the driver path predeclares the
  real signature. Hence the placeholder filters.

Pinned by `test/01_unit/compiler/semantics/resolve_methods_quiet_typed_spec.spl`
— 5/5 green: loud pass errors on the untyped receiver (Gap B baseline); quiet
pass records ZERO errors on the same module; annotated-Let receiver is typed
`Dict` after the quiet pass; placeholder types are never stamped; the default
(loud/bootstrap) walk leaves receiver nodes byte-identical.

### 4. Blast radius of turning resolution on

- MIR's `lower_method_call` handles a positive resolution in its terminal
  `match resolution` (`method_calls_literals.spl:2715+` InstanceMethod arm =
  direct `emit_call` with the callee's real return type). The `resolution_is_unresolved`-gated fallbacks (17 uses in gating/condition position; 15 boolean-condition sites, measured) stop firing ONLY for calls that
  became resolved — by construction those are calls the resolver proved to be
  user-type instance/trait/static methods.
- The dict-name and predicate probes deliberately DISTRUST positive
  resolutions (the "Dict `.has` resolved to unrelated `DiContainer.has`"
  incident is documented in that file) and re-probe the lowered receiver —
  they remain as backstop and are safe to leave in place.
- Residual risk is exactly one class: a WRONG positive resolution (same-named
  method on an unrelated owner). Mitigated by type-directed owner-scoped
  lookup and contained by the flag; this is the thing to watch in the flag-on
  error-count measurement.

### 5. Estimate: CONTAINED for the declared/structural tier; the rest is real work

- Tier 1 (landed): resolver-side attach + Let backfill + quiet wiring — 6
  files, ~150 lines, no construction-site changes, default-off. Evidence it
  is contained: it is done, green on its spec, and flag-off is byte-identical
  (`resolve_nil_guard_spec` 6 passed / 5 failed both before and after — the 5
  are pre-existing host failures, identical at pristine HEAD).
- Tier 2 (bounded, days not weeks): `Field` arm in `infer_expr_type` (struct
  field-type lookup), match-binding registration, tuple-index — each extends
  the same helper + env, no new pass.
- Tier 3 (the genuine refactor, weeks): full inference-backed writeback —
  requires either HM writeback via a rebuilding traversal (no node ids) or
  running resolution inside inference; touches `30.types` + `20.hir`
  contracts. NOT needed to un-block the MCP error families if measurement
  shows tiers 1-2 cover the receiver provenances actually failing.

### Measurement status (honest)

- Mechanism-level measurement: done (the 5-scenario spec above; loud pass =
  errors on the repro, quiet pass = 0 errors + typed receiver).
- End-to-end MCP error count flag-on vs flag-off: **BLOCKED ON THIS HOST.**
  The fresh Windows seed SEGVs (rc=139, after `[engine-demotion]
  hybrid-interp-splice`) merely LOADING the full driver module graph
  (`use compiler.driver.driver` from a 5-line file) — reproduced at pristine
  HEAD with all five edited files restored to `git show HEAD:`, so it is
  pre-existing and not caused by this change. The same graph loads fine via
  `simple test` on unit specs that stop at frontend+HIR+semantics. Whoever
  holds a Linux lane should run the same MCP native-build used for the
  133-error baseline with `SIMPLE_RESOLVE_METHODS=1` and diff the counts;
  the `[resolve-methods-quiet]` receipt line proves the pass ran.
