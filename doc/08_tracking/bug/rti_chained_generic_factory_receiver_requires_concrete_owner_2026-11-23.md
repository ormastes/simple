# RTI chained generic-factory receivers require a concrete owner

Status: RTI owner-discovery boundary repaired (2026-11-25, verified under `--mode=interpreter`); MIR outer-subject fallback for non-concrete generic method matches and native self-build verification remain open (see 2026-11-25 section below).
This is separate from the repaired explicit generic free-call argument loss.
Indexed generic method return prescan and Future static-factory issues were
consulted; neither describes this exact RTI receiver boundary. No indexed
claim was created or a stalled claim command retried.

A candidate reproduction is an erased generic caller using
`factory<T>().get()` when the factory declares `Store<T>` and the store's
method return depends on T. A concrete `factory<text>().get()` is a distinct
control; a local `store` variable is the production fourteen-module fixture's
shape and does not traverse this chained receiver path.

In `src/compiler/20.hir/return_type_interface_v1.spl`,
`receiver_owner_with_args` first accepts an independently declared receiver
type. Without one, its chained-expression fallback calls
`callee_return(receiver, symbols, None)` and immediately invokes
`resolve`/`require_concrete`. It does not carry the active caller's declaration
binders into that nested call. Even before explicit argument handling, a
generic factory return containing a provider Param failed this concrete
requirement with E-RTI-003. That error propagated through `method_return` to
MIR's outer fatal error branch. Consequently this shape was already rejected;
the free-call repair does not establish support for it.

Passing caller binders alone cannot repair the boundary: the legitimate
`Store<T>` receiver still contains caller Params and is not concrete. A future
owner repair must preserve the independently proven nominal Store identity,
carry caller binders through nested calls, and substitute method results in
that scoped symbolic context. It must reject unrelated/unbound parameters and
missing nominal owners. Broadly treating outer E-RTI-003 errors as successful
lookup would hide other ownership errors and is not an acceptable repair.

Required regression evidence: a real parsed imported factory and generic
owner method, positive concrete and erased-generic chains, negative unbound
caller parameters and missing owners, nested parameter containers, and exact
native output with the verified producer. No workaround, guard change, or
runtime PASS is supplied by this report.

## 2026-11-25 — RTI nominal owner discovery repair

Repaired `receiver_owner_with_args` in `src/compiler/20.hir/return_type_interface_v1.spl`:

- When `self.resolve(self.callee_return(receiver, symbols, nil, consumer_params)?)?` produces `ReturnTypeEntry.Decided(RtType.Nominal(decl, args))`, `receiver_owner_with_args` now returns `Ok((decl, false, args))` directly instead of calling `self.require_concrete(resolved)?`.
- Caller parameters (and nested parameter containers) inside `args` flow into `method_return` and `rti_apply_owner_args_v1` in the `consumer_params` binder context (`95598705f45` already threaded `consumer_params` through `method_return`, `receiver_owner_with_args`, `static_or_value_owner`, and `rti_owner_args_v1`).
- Concrete-consequence boundaries remain unchanged: builtin non-owner heads still fail with `E-RTI-001` via `rti_term_head_may_own_methods_v1`, bare `RtType.Param` / `Union` / unresolved `AsyncRef` still go through `require_concrete` (`E-RTI-003` / `E-RTI-002`), unbound caller parameters fail with `E-RTI-007`, missing nominal arguments fail with `E-RTI-004`, missing nominal owner/method rows fail with `E-RTI-001` at `self.lookup(...)`, and outer consumers still enforce `require_concrete` on the specialized method return.

Verified under `--mode=interpreter` in `test/01_unit/compiler/hir/rti_chained_nominal_owner_spec.spl`:

- Parsed imported `lib.store` (`Boxed<W>`, `Store<K, V>`, `make_store<K, V>`, `make_bool_store<K>`, `ident<T>`) + consumer:
  - Concrete chain `make_store<i64, text>("hi").get_res()` -> `result(b:text,b:text)` (passes strict MIR too).
  - Mixed generic+concrete chain `make_bool_store<K>(true).remove(key)` -> `opt(b:bool)` (passes non-strict MIR).
  - Erased-generic chains `make_store<i64, T>(v).flag()` -> `b:bool`, nested parameter container `make_store<i64, Result<T, text>>(Ok(v)).wrap().label()` -> `b:text`, `make_store<i64, T>(v).get_res()` -> `Ok(Decided(result(p0,b:text)))` (`E-RTI-003` only at outer `require_concrete`), `make_store<i64, Option<T>>(Some(v)).wrap().unbox()` -> `Ok(Decided(opt(p0)))`, and `.get_opt().is_some()` / `.get_res().is_ok()` -> `E-RTI-001` (`is not a struct/class`), passing non-strict MIR.
  - Negative controls: unbound caller parameters (`E-RTI-007`), missing nominal args (`E-RTI-004`), missing owner/method rows (`E-RTI-001`), bare `Param` (`E-RTI-003`), builtin non-owner heads (`E-RTI-001`), and `Union`/`AsyncRef` (`E-RTI-002`).

Remaining outer/MIR-side and native-validation gaps:

- **Outer MIR `match` fallback for non-concrete erased generic method results**: for `match make_store<i64, T>(v).get_res():` where `get_res() -> Result<V, text>`, RTI succeeds with `Decided(result(p0,b:text))` and outer `require_concrete` falls through with `E-RTI-003`, after which `enum_match_subject_type` (`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:3304-3338`) inspects the uninstantiated retained local type `Result<TypeParam("V"), Str>` via `function_signature_ownership_proof` and emits `"enum match retained Result/Optional has no complete declaration ownership"`. Concrete-slot chains (`make_bool_store<K>(true).remove(key)`), scalar/nominal chains (`.flag()`, `.label()`), and `.is_some()`/`.is_ok()` chains do not hit this.
- **`SIMPLE_RTI_STRICT=1` on inner generic nominal receivers**: `method_calls_literals.spl` calls `enum_match_expr_type(receiver)` on the inner receiver of a `MethodCall` (e.g. `make_bool_store<K>(true)` inside `make_bool_store<K>(true).remove(key)`), which hits `require_concrete` on `Nominal(Store, [Param(0), Builtin("bool")])`. Non-strict MIR falls through cleanly; `SIMPLE_RTI_STRICT=1` rejects that intermediate check.
- **Lifted lambdas**: `switch_operators_calls.spl:9095` does not copy `current_rti_consumer_params` onto child `MirLowering` instances.
- **Native verification**: native Stage 2/3 compilation and exact native runtime output remain pending a native build lane.
