# Research C: Cranelift Instr Lowering — Duplication Map

Scope: `src/compiler_rust/compiler/src/codegen/instr/` (25 `.rs` files)
Date: 2026-04-28
Analyst: Phase-2 sub-agent (Sonnet)

---

## Summary

Two real clusters found; one candidate filtered out by the anti-over-engineering
rule. The dominant pattern is `runtime_funcs[name] + declare_func_in_func +
adapted_call` repeated verbatim across ~18 files. `methods.rs` already solved
this in-file with private helpers `call_runtime_1/2/3/2_void`; those helpers
need to be promoted to `helpers.rs` as `pub(crate)`. The second cluster is a
repeated N-param-i64 dynamic signature build (cache-check + declare_function)
spread across 5 files; it can be unified with one helper, with one site
(`closures_structs.rs:492`) staying open-coded due to an `or_else` N-1 fallback.

---

## Cluster 1: `call_runtime_N` — runtime func lookup + declare + call

- **Call sites** (representative — full list is ~74 open-coded sites across 17
  files; counts from grep):
  - `actors.rs:32-34`, `actors.rs:43`, `actors.rs:58-60`, `actors.rs:75`,
    `actors.rs:91-92`, `actors.rs:107-108`, `actors.rs:115`
  - `async_ops.rs:28-30`, `async_ops.rs:122`
  - `collections.rs` — 21 `declare_func_in_func` calls, most follow the pattern
  - `core.rs` — 13 `declare_func_in_func` calls
  - `simd_stubs.rs` — 12 calls
  - `body.rs` — 11 calls
  - `enum_union.rs:40-46`, `enum_union.rs:57-63`, `enum_union.rs:74-80`
  - `pattern.rs:112-118`
  - `parallel.rs`, `pointers.rs`, `result.rs`, `coverage.rs`, `memory.rs`
  - (methods.rs itself has ~22 open-coded sites outside the regions already
    using `call_runtime_1/2/3`)
  - Existing in-file helpers (private): `methods.rs:14-68`
    `call_runtime_1`, `call_runtime_2`, `call_runtime_2_void`, `call_runtime_3`

- **Shared invariant**: every site executes exactly:
  ```rust
  let func_id = ctx.runtime_funcs[name];            // FuncId already cached
  let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
  let call = adapted_call(builder, func_ref, &[…]);
  // optionally: builder.inst_results(call)[0]
  ```
  No signature is ever built here; `runtime_funcs` already holds pre-declared
  `FuncId`s. The arity distribution across all open-coded sites is:
  arity-0: 3 sites, arity-1: ~22 sites, arity-2: ~39 sites, arity-3: ~10
  sites, arity-4+: a small handful. Arities 1-3 and 2-void cover >90% of sites.

- **Proposed unification**: move the existing four helpers from `methods.rs` to
  `helpers.rs` as `pub(crate)`, add a `call_runtime_0` (void-args variant) and
  a `call_runtime_1_void` for the arity-0/void cases, keep arity-4+ open-coded
  at the handful of sites where they occur (anti-over-engineering: those few
  sites don't justify a varargs wrapper):

  ```rust
  // helpers.rs — owner of all call_runtime_N helpers
  #[inline]
  pub(crate) fn call_runtime_0<M: Module>(
      ctx: &mut InstrContext<'_, M>,
      builder: &mut FunctionBuilder,
      func_name: &str,
  ) {
      let func_id = ctx.runtime_funcs[func_name];
      let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
      adapted_call(builder, func_ref, &[]);
  }

  #[inline]
  pub(crate) fn call_runtime_1<M: Module>(
      ctx: &mut InstrContext<'_, M>,
      builder: &mut FunctionBuilder,
      func_name: &str,
      arg: cranelift_codegen::ir::Value,
  ) -> cranelift_codegen::ir::Value {
      let func_id = ctx.runtime_funcs[func_name];
      let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
      let call = adapted_call(builder, func_ref, &[arg]);
      builder.inst_results(call)[0]
  }

  // call_runtime_2, call_runtime_2_void, call_runtime_3 — same shape
  // (already exist in methods.rs; copy verbatim, add #[inline])
  ```

  Owner file: `helpers.rs`. All callers import from `super::helpers`.

- **Risk**:
  - **Hot-path inlining**: `methods.rs` helpers are plain `fn` (no `#[inline]`).
    Because `rustc` won't inline cross-module `pub(crate)` functions by default,
    add `#[inline]` on each helper to preserve parity with the previous inlined
    open-coded version. Without `#[inline]`, Cranelift's own JIT function call
    overhead could appear in profiling for `collections.rs` and `core.rs` which
    are in tight codegen loops.
  - **Panic attribution**: if `ctx.runtime_funcs[name]` panics (missing key),
    the error currently prints nothing identifying the call site. The helper
    should use `.unwrap_or_else(|| panic!("missing runtime fn '{}' in {}", name, ctx.func.name))`
    for debuggability parity with `get_vreg_or_default`'s `SIMPLE_STRICT_VREG`
    path.
  - **Type drift**: no risk — all `runtime_funcs` entries are pre-declared with
    uniform I64 signatures; the helpers don't touch signature construction.

- **Test surface**:
  - Existing: `test/` spec files that exercise arrays, dicts, actors, closures,
    generators, enums — these all go through the affected files. Run
    `bin/simple test` in interpreter mode (per memory `compile_mode_false_greens`,
    interpreter mode gives true pass/fail).
  - Intensive regression: add a spec that calls every builtin method family
    (Array.push/pop/clear, Dict.set/get/keys, tuple.get, string.concat, enum
    construction) in a single test file, checking return values. This exercises
    every caller file of the promoted helpers. Run in both interpreter and
    native modes; the native mode catch would be an `#[inline]` regression
    (missing result from `inst_results` if arity mismatch).

---

## Cluster 2: Dynamic-resolve sig build + declare_function (uniform I64)

- **Call sites** (5 sites in 4 files; one site excluded — see Risk):
  - `calls.rs:698-711` — builds `n`-param I64 sig, checks `func_ids` cache,
    declares import, caches result
  - `methods.rs:309-321` — same shape, `n = args.len() + 1` (receiver + args)
  - `closures_structs.rs:65-79` — same shape, `n = 1` (closure pointer only),
    with explicit cache check
  - `mod.rs:232-241` — same shape, `n = 1`, emits `func_addr` instead of call
    (still reuses the declare pattern)
  - **Excluded site**: `closures_structs.rs:492-520` has an `or_else` N-1
    fallback (tries `n+1` params first, then `n` params on error). A helper
    taking `(name, n_params)` cannot replicate this without a `fallback_n:
    Option<usize>` parameter that would push total parameters to 4+ and make
    the helper harder to read than the open-coded version. Per the
    anti-over-engineering filter, this site stays open-coded.

- **Shared invariant**: every included site:
  1. checks `ctx.func_ids.get(name)` for a cached `FuncId`
  2. if miss: builds `Signature::new(platform_call_conv())` with `n` I64 params
     and one I64 return
  3. calls `ctx.module.declare_function(name, Linkage::Import, &sig)`
  4. inserts result into `ctx.func_ids`
  5. calls `ctx.module.declare_func_in_func(func_id, builder.func)`

- **Proposed unification**: one helper in `helpers.rs`:

  ```rust
  /// Look up or declare an import function with `n_params` I64 params → I64 return.
  /// Returns the `FuncRef` for use in the current function body.
  /// Caches the `FuncId` in `ctx.func_ids` to avoid Cranelift "incompatible
  /// declaration" errors on re-declaration.
  #[inline]
  pub(crate) fn declare_uniform_i64_import<M: Module>(
      ctx: &mut InstrContext<'_, M>,
      builder: &mut FunctionBuilder,
      name: &str,
      n_params: usize,
  ) -> cranelift_codegen::ir::FuncRef {
      use cranelift_codegen::ir::{types, AbiParam, Signature};
      use cranelift_module::{Linkage, Module};
      use crate::codegen::shared::platform_call_conv;

      let func_id = if let Some(&existing) = ctx.func_ids.get(name) {
          existing
      } else {
          let mut sig = Signature::new(platform_call_conv());
          for _ in 0..n_params {
              sig.params.push(AbiParam::new(types::I64));
          }
          sig.returns.push(AbiParam::new(types::I64));
          let id = ctx.module
              .declare_function(name, Linkage::Import, &sig)
              .unwrap_or_else(|_| {
                  // Already declared (e.g. as Export); retrieve existing id.
                  match ctx.module.get_name(name) {
                      Some(cranelift_module::FuncOrDataId::Func(id)) => id,
                      _ => panic!("declare_uniform_i64_import: '{}' not a function", name),
                  }
              });
          ctx.func_ids.insert(name.to_string(), id);
          id
      };
      ctx.module.declare_func_in_func(func_id, builder.func)
  }
  ```

  Owner file: `helpers.rs`. The `mod.rs` site additionally calls
  `builder.ins().func_addr(...)` after getting the `FuncRef`; that one line
  stays at the call site.

- **Risk**:
  - **ABI divergence**: all 4 included sites use I64-only signatures. If a
    future site needs mixed types (e.g., F64 param), it cannot use this helper.
    The helper's name (`declare_uniform_i64_import`) makes the constraint
    explicit.
  - **The `or_else` exclusion**: `closures_structs.rs:492` has a real
    behavioural difference (N-1 fallback). Unifying it would require an optional
    `fallback_n` param — 4+ parameters, anti-over-engineering filter applies.
    Leave it open-coded with a comment pointing to the helper for the common case.
  - **Calling-convention drift**: `crate::codegen::shared::platform_call_conv()`
    is used at all 4 included sites; the helper centralises this, so a future
    per-platform CC change only needs one edit.

- **Test surface**:
  - Existing: cross-module method call specs, closure-call specs, trait dispatch
    specs (any spec that exercises `use SomeType` in another module triggers
    the dynamic-resolve path). Run in interpreter mode.
  - Intensive regression: a spec with a class defined in module A, imported and
    called in module B, exercising a method with 0, 1, 2, and 3 arguments.
    This exercises `calls.rs`, `methods.rs`, and `closures_structs.rs` dynamic
    paths simultaneously. Run in both interpreter and native modes.

---

## Filtered Candidate: `import_signature` + `indirect_call_with_result` in `closures_structs.rs`

Two sites exist:
- `closures_structs.rs:123-132` (closure indirect call, typed sig)
- `closures_structs.rs:882-891` (vtable trait method call, typed sig)

Both build `Signature::new(platform_call_conv())`, push receiver + typed params
(using `type_id_to_cranelift`), optionally push a typed return, then call
`builder.import_signature` and `indirect_call_with_result`.

**Filter result**: Only 2 call sites, both in the same file. Per AC-5 ("fewer
than 3 call sites AND no shared invariant across files"), this is a valid
intra-file extract but does not meet the cross-file dedup bar. The two sites
also differ in how they resolve the function pointer (closure slot 0 vs vtable
slot N). An intra-file private helper is reasonable but is out of scope for
this pipeline's dedup criteria. The Phase-3 architect may elect to include it
as a self-contained intra-file cleanup in the same commit as Cluster 1.

---

## Files Inspected

All 25 `.rs` files in `src/compiler_rust/compiler/src/codegen/instr/`:
`actors.rs`, `async_ops.rs`, `basic_ops.rs`, `body.rs`, `calls.rs`,
`closures_structs.rs`, `collections.rs`, `constants.rs`, `contracts.rs`,
`core.rs`, `coverage.rs`, `enum_union.rs`, `extern_classes.rs`, `fields.rs`,
`helpers.rs`, `interpreter.rs`, `memory.rs`, `methods.rs`, `mod.rs`,
`parallel.rs`, `pattern.rs`, `pointers.rs`, `result.rs`, `simd_stubs.rs`,
`units.rs`.

Key counts driving cluster decisions:
| Pattern | Files with occurrences | Total sites |
|---------|----------------------|-------------|
| `runtime_funcs[x] + declare_func_in_func + adapted_call` | 17 | ~74 open-coded |
| `call_runtime_N` helpers (private) | 1 (methods.rs) | 15 call sites |
| dynamic uniform-I64 `declare_function` + cache | 4 | 4 sites (5th excluded) |
| `import_signature` + `indirect_call_with_result` | 1 (closures_structs.rs) | 2 sites |
