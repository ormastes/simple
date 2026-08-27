# JIT: a named fn used as a value bails the WHOLE stage1 compiler to the interpreter

- **Filed:** 2026-08-22
- **Status:** FIXED (seed, Rust) — see "Fix" and "Evidence"
- **Severity:** High (perf) — stage1 `native-build` ran 100% on the tree-walker
- **Component:** Rust seed JIT — `src/compiler_rust/compiler/src/codegen/{jit.rs,cranelift_emitter.rs,closure_boxed_entry.rs}`
- **Parent records:** `hir_phase_per_module_cost_2026-08-21.md` (7th session),
  `jit_closure_abi_refuses_lambdas_and_miscompiles_fn_refs_2026-08-06.md` (defect 2)

## Symptom

The seed's `run` is whole-program JIT-or-nothing (`driver/src/exec_core.rs`).
The bootstrap log for stage1 shows exactly one bail:

    Cranelift JIT compile: Module error: function '_make_noop_lexer' loads a
    named function as a callable value; the JIT closure ABI has no tag-boxed
    representation for a bare function pointer

from `src/compiler/00.common/compiler_services.spl:168`
(`LexerPort(tokenize_fn: _noop_tokenize)`). Fn-ref ports are a design choice
(MDSOC ports); the defect is on the seed side. Result: ~1,500 compiler files
interpreted at ~2 us/statement, ~10 us/call (`define` 12 us JIT vs 320-470 us
interpreted, ~30x).

Reproduce pre-fix (seed `5ff4999c8e9`):

    SIMPLE_TIMEOUT_SECONDS=0 bin/simple run <fixture with Port(f: named_fn)>
    [INFO] JIT compilation failed, falling back to interpreter: ... function
    'make' loads a named function as a callable value ...

## Root cause

`emit_global_load` resolved a function-valued identifier to a BARE
`func_addr`; `compile_indirect_call` expects a `RuntimeClosure` handle and
goes through `rt_closure_func_ptr` to a tag-boxed entry. The 2026-08-07 guard
(`first_named_fn_value_load`) correctly refused the module instead of
miscompiling — but for EVERY defined function, including ones with a body and
full static types, which is exactly the case that IS representable.

## Fix (seed, semantics-preserving, no Simple-side change)

1. `closure_boxed_entry.rs`: `emit_boxed_entry_for(func, has_ctx)` generalises
   the lambda thunk. `emit_boxed_fn_value_entries(mir, functions)` emits a
   `name$boxed` thunk (tagged `RuntimeValue` in/out, forwards only user args)
   for every DEFINED function that any `GlobalLoad` references as a value
   (`named_fn_value_targets`, same resolution as the guard).
2. `cranelift_emitter.rs::emit_global_load`: when `name$boxed` exists, emit
   `rt_closure_new(func_addr(name$boxed), 0)` — a real zero-capture closure
   object, identical in representation to a lambda value. Works for indirect
   calls from JIT code AND for runtime helpers (`rt_array_map` etc.).
3. `jit.rs::first_named_fn_value_load`: refusal narrowed to bodiless/extern
   names (still no representation). Lambdas keep their own guard unchanged.

## Evidence

- `src/compiler_rust/compiler/tests/fn_ref_value_jit.rs` — asserts
  `compile_module` returns Ok (pre-fix: Err with the text above) and the
  calls answer correctly for i64/bool/f64 params, local fn value, fn passed
  as arg, and the stage1 Port-struct shape. Failing pre-fix, green post-fix.
- Fixture run post-fix: no `[INFO] JIT compilation failed` line, output
  byte-identical to the interpreter (`2 / x / true / 3.0 / 42 / 3`).
- Perf gate: `scripts/check/check-perf-regression-tests.shs` rows `FNREFJIT`.
- Measurement: see "Measurement" below.

## Measurement and remaining gate

Stage1 entry (`bootstrap_main.spl compile hello.spl --format=smf`) under the
fixed seed: the fn-ref refusal is gone and Cranelift now compiles the whole
stage1 closure, but it still falls back because 6 bodies fail with
`[CODEGEN-AMBIGUOUS-METHOD]` (bare method on an `Any` / trait-object receiver:
`BlockRegistry.register`, `register_block`, `with_block` -> `block_def.kind()`
with `block_def: Any`; `objtaker_take_object/_with_types/_concrete` ->
`smf_reader.lookup_symbol/read_code` on the `SmfReader` trait). The seed JIT
has no dynamic dispatch for erased receivers; that is a separate defect class
and the next lever. Until it lands, `driver_types.spl` registration wall is
unchanged by construction (still interpreted), so no before/after number is
claimed here. Wall for the hello compile (load ~30): old seed 63 s, new seed
81-162 s — both fully interpreted, the spread is box load, not the change.

Also found and removed on the way: the tree had grown a SECOND, EARLIER gate
since the 7th session — `declared_imported_surface_signature_type`
(`20.hir/hir_lowering/_Items/module_callable_types.spl`, from 659134f5762)
referenced a field and a helper that do not exist (`signature_names`,
`module_surface_signature_arrays_aligned`): zero callers, dead under the
interpreter, a fatal HIR-lowering error under JIT that fired BEFORE the
Cranelift guard. Deleted.
