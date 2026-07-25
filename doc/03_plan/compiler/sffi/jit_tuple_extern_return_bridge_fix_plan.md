# Plan: JIT/AOT composite extern-return bridge (tuple/text/f64)

- **Status:** Implemented for tuple + text returns; verified live in default JIT.
  `MirInst::InterpCall` gained a `boxed_result` flag set by the hybrid transform
  (`compilability::boxed_return_functions` walks `Node::Function`/`Node::Extern`
  return types); cranelift `compile_interp_call` skips the `rt_value_raw_i64`
  unbox when set; `value_to_runtime` now marshals `Value::Tuple` as a real
  `rt_tuple`. Verified: `val (status, body, err) = rt_http_request(...)` against
  live MinIO returns `(403, <254B>, "")` under default JIT, read correctly by
  destructuring and `.0`. Arrays/options/generics/f64 remain conservative
  (unboxed) future extensions. `.N` access on a *text* tuple field is a separate
  pre-existing bug, unchanged.
- **Date:** 2026-06-16
- **Area:** compiler/codegen (cranelift + llvm), mir/hybrid, runtime_bridge
- **Related bug:** [[itf_minio_sigv4_not_runnable_interp_or_native_2026-06-16]]
- **Severity:** P2 (correctness; silent garbage, not a crash)

## Problem

When JIT/AOT-compiled code calls a runtime extern that is routed to the
interpreter (the `MirInst::InterpCall` / `rt_interp_call` bridge), the result is
a NaN-boxed `RuntimeValue`. Codegen then **unconditionally unboxes it to a raw
i64** for every `rt_*`/`spl_*` name. That is correct for scalar returns
(`bool`/`i64`/handle) but **corrupts any composite or non-i64 return**
(tuple, text, array, struct, f64): the boxed heap pointer is stripped of its tag,
so a subsequent `rt_tuple_get`/`rt_string_*` reads garbage.

Net effect: every tuple/text-returning `rt_*` extern is broken under the default
JIT run mode. Verified live: `rt_http_request` and the pre-existing `rt_http_get`
both return `(403, <body>, "")` correctly under `SIMPLE_EXECUTION_MODE=interpret`
but yield `R0:0` / `<value:0xffffffffffffffff>` under default JIT.

## Root cause (exact)

1. `codegen/instr/core.rs:783-788` (`compile_interp_call`, cranelift):
   ```rust
   let is_extern_bridge = func_name.starts_with("rt_") || func_name.starts_with("spl_");
   let value = if is_extern_bridge || vreg_is_native_equality_scalar(ctx, *d) {
       call_runtime_1(ctx, builder, "rt_value_raw_i64", result)  // <-- unbox to raw i64
   } else {
       result
   };
   ```
   The in-code comment already names the gap: *"Known gap: f64/text extern
   returns are not representable through this bridge yet."* Tuple is the same
   class of gap.
2. The LLVM backend has the equivalent path
   (`codegen/llvm/functions/calls.rs::compile_interp_call` ~2526,
   `codegen/llvm/emitter.rs::emit_interp_call` ~456) and must be fixed in lockstep.
3. `MirInst::InterpCall { dest, func_name, args }` (`mir/instructions.rs`,
   constructed in `mir/hybrid.rs:42`) **carries no return type** — the hybrid
   transform drops the `Call`'s `target: CallTarget`, and `CallTarget`
   (`mir/effects.rs:541`) only exposes `.name()`. So codegen has nothing but the
   name to decide on, hence the `starts_with("rt_")` heuristic.
4. `runtime_bridge::value_to_runtime` currently marshals `Value::Tuple` as an
   **array** (`rt_array_new`), so even once the result is kept boxed,
   `rt_tuple_get` relies on its lenient array fallback. Marshalling tuples as
   real `rt_tuple_new` tuples is the correct, robust pairing.

## Fix design

Decide unbox-vs-keep-boxed by the extern's **declared return type**, not by name.

1. **Carry return-type intent into `InterpCall`.** Add a field to
   `MirInst::InterpCall` — minimal form `boxed_result: bool` (true = keep boxed,
   false = unbox to raw i64), or richer `ret_kind: InterpRetKind {Scalar, F64,
   Boxed}` if f64 needs a distinct unbox (`rt_value_raw_f64`). Populate it in
   `mir/hybrid.rs::transform_function` from the call site's known signature.
   - Source of truth: the extern/function return type is available where
     `non_compilable_functions` is computed (typed AST / extern decl table). Thread
     a `HashMap<String, RetKind>` (or augment the existing non-compilable set into
     a map) so the transform can stamp each `InterpCall`.
   - A return type is "boxed" when it is tuple / text / array / struct / option /
     any heap type; "scalar" when `i8..i64`/`bool`/handle/ptr; "f64" for floats.
2. **Type-aware unbox in both backends.** Replace the `starts_with("rt_")`
   heuristic in `compile_interp_call` (cranelift core.rs and the two LLVM sites)
   with the `InterpCall` field: unbox scalars via `rt_value_raw_i64`, floats via
   the f64 unbox, keep boxed for composite. Preserve today's scalar behaviour
   exactly (the NaN-boxed-`false`-reads-truthy hazard the comment warns about).
3. **Marshal tuples as tuples.** Reapply the `value_to_runtime` change (revert of
   `runtime_bridge.rs` from commit `efcffcd`): `Value::Tuple` →
   `values_to_runtime_tuple` (`rt_tuple_new`/`rt_tuple_set`). Update the existing
   `test_value_to_runtime_tuple_as_indexable_array` test, which currently asserts
   array semantics, to assert tuple semantics (`rt_tuple_len`/`rt_tuple_get`).

## Affected files

- `mir/instructions.rs` — add field to `InterpCall`.
- `mir/hybrid.rs` — populate the field; signature of `apply_hybrid_transform` /
  `transform_function` gains a ret-type lookup.
- caller of `apply_hybrid_transform` — build/thread the ret-type map alongside
  `non_compilable_functions`.
- `codegen/instr/core.rs` — type-aware unbox (cranelift).
- `codegen/llvm/functions/calls.rs` + `codegen/llvm/emitter.rs` — type-aware
  unbox (LLVM).
- `codegen/runtime_bridge.rs` — tuple marshalling + test update.

## Risks / regression surface

- **Scalar regression is the main risk.** Every existing compiled `rt_*` scalar
  extern depends on the current unbox. The new field must classify those as
  `Scalar` so their codegen is byte-identical. Add a guard: default to `Scalar`
  (unbox) when ret type is unknown, so unmapped externs keep today's behaviour.
- f64 externs are a pre-existing separate gap; closing it is optional in this
  change but uses the same mechanism. If deferred, classify f64 as `Boxed` only
  if a tested f64 unbox exists, else leave as `Scalar` and note it.
- Two backends must stay in lockstep or AOT vs JIT diverge.

## Test plan

- Unit: `codegen` tests asserting an `InterpCall` with a tuple return keeps the
  boxed result (no `rt_value_raw_i64`), and a scalar return still unboxes.
- Runtime: a spec that calls `rt_http_request` against a local server and
  destructures `(status, body, err)` under **default JIT** (not just interpret).
  Gate behind an env/feature so CI without a server skips it; mirror the
  interpret-mode probe already proven in the bug doc.
- Regression: full bootstrap + existing scalar-extern specs (bool/i64 `rt_*`)
  must be unchanged.

## Effort

Medium. The mechanism is small and local, but it touches the MIR instruction
shape, the hybrid transform's signature, and three codegen sites across two
backends, plus a bootstrap rebuild to verify. ~1 focused session.
