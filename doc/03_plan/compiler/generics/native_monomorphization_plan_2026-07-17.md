# Native-Path Monomorphization — Staged Plan (#158 Phase B)

Status: Phase A (loud fail-closed) COMPLETE for all reached tiers. Phase B
(actual monomorphization) NOT attempted — deferred with this plan. Written by
lane S48, 2026-07-17.

## What Phase A now guarantees (no silent miscompiles)

Every generic construct that reaches native lowering fails **loud** (build
`rc=1`, no binary emitted), never a silent wrong answer:

| Tier | Gate site | Message prefix |
|------|-----------|----------------|
| Generic free fn `fn id<T>(x: T) -> T` | `20.hir/hir_lowering/_Items/declaration_lowering.spl:198` | `generic functions are not supported on the native build path yet` |
| Generic struct `struct Box<T>: v: T` | `20.hir/hir_lowering/_Items/declaration_lowering.spl` (`lower_struct`, `struct_type_params.len() > 0`) — **added by S48** | `generic structs are not supported on the native build path yet` |
| Generic class `class Box<T>: v: T` | `20.hir/hir_lowering/_Items/declaration_lowering.spl` (`lower_class`, `class_type_params.len() > 0`) — **added by S48** | `generic classes are not supported on the native build path yet` |
| Generic struct/class method | `20.hir/hir_lowering/_Items/trait_impl_lowering.spl:168` | `generic struct/class methods are not supported on the native build path yet` |

All three gate at HIR lowering (phase 3), the earliest layer where
`Function.type_params` / `Struct.type_params` are threaded and reliably present.
This precedes MIR (phase 5), so no unmonomorphized `T` reaches codegen.

### Residual silent tiers (NOT yet loud — accidental-correct, not miscompiling)
- **Generic enums** `enum Wrap<T>: Val(T)` — currently build `rc=0` and print
  correctly for `i64` and `text` (payloads are boxed runtime values, so they
  round-trip). NOT gated because (a) not a demonstrated miscompile and (b)
  `Option<T>`/`Result<T>` are generic enums with dedicated MIR kinds; a blanket
  `lower_enum` type-param gate risks those fundamentals. Gate only after
  confirming the enum path does not alias Option/Result lowering.
- **Multi-type-param free fns** and **trait-bounded free fns** already hit the
  free-fn gate (`type_params.len() > 0`), so they are loud today.

## Why the silent generic-struct bug existed (root chain)

1. Parser keeps `<T>` as a `[text]` name list, rebuilt into `[TypeParam]` by the
   flat-AST bridge (`10.frontend/_FlatAstBridge/convert_nodes.spl:1473`,
   `module_assembly.spl:281`) — not dropped.
2. HIR resolves a param/field `T` to `HirTypeKind.Named(TypeParam_symbol)`
   (`20.hir/hir_lowering/types.spl:435-440`; the unresolved fall-through
   `types.spl:441-446` is already diagnosed).
3. MIR `lower_type` `case Named(symbol,_)` →
   `MirTypeKind.Struct(symbol)` (`50.mir/_MirLowering/function_lowering.spl:492`)
   with no TypeParam guard. Backend treats `Struct(_)` as an opaque pointer
   local (`70.backend/backend/_MirToLlvm/core_codegen.spl:256`). A `text` field
   stored in a pointer-width slot was truncated and read back as a garbage
   integer (e.g. `105768476834283`).

A generic **class** (MDSOC+ default aggregate) took the sibling `lower_class`
path with no gate: instead of silent garbage it bailed during codegen and
surfaced only as a cryptic `ld.lld: cannot open ...p_class.o: No such file`
link error naming neither the class nor #158. The `lower_class` gate now makes
it a clean precise HIR failure too.

Note: a MIR-level `Named(TypeParam)` guard was tried first but is DEAD for
structs — struct field types are laid out by field-count/name, not routed
through `function_lowering.lower_type`, so the gate never fired. The HIR
declaration gate is the correct, proven-fatal layer.

## Phase B — staged monomorphization for the simplest real tier

Target tier only: **free function, one type parameter, concrete arg-inferable
call site** (`id(5)`, `id("x")`). No trait bounds, no variance, no generic
structs/enums, no generic methods.

### Existing infrastructure to EXTEND (do not reinvent)
- Entry: `run_monomorphization(modules: Dict<text, HirModule>) -> (Dict<text, HirModule>, MonoStats)`
  at `40.mono/monomorphize_integration.spl:502`, wired as driver Phase 4
  (`80.driver/driver.spl:314` → `monomorphize_impl` `:940` → `:952`), runs
  before MIR. Skippable via `SIMPLE_BOOTSTRAP_SKIP_MONO`.
- Primitives that already exist: `specialize_function_with_types(func, type_args)`
  (`40.mono/monomorphize/engine.spl:172`), `substitute_function/type/expr`
  (`40.mono/monomorphize/type_subst.spl`), `generate_mangled_name`/`mangle_type`
  (`engine.spl:191-231`), `check_generic_call` (`integration.spl:351`).
- Data model: `HirModule.functions: Dict<SymbolId, HirFunction>`
  (`20.hir/hir_types.spl:26`); call node
  `HirExpr.Call(callee, args, type_args:[HirType])`
  (`20.hir/hir_definitions.spl:465`) — `type_args` already carried.

### Known stubs that MUST be implemented (all in 40.mono)
- `monomorphize_integration.spl:395-401` `rewrite_module` returns the module
  unchanged (no specialized defs added, no call sites rewritten).
- `monomorphize_integration.spl:388` `process_specializations` "skip actual
  specialization (requires type casting)".
- `engine.spl:163-165` `monomorphizer_specialize_function_internal` returns
  `func` as-is.
- `type_subst.spl:34` returns `HirTypeKind.Error` for every substitution.
- HIR functions are stored as `Any` in `MonomorphizationTable`, blocking
  `specialize_function_with_types` from being invoked on a real `HirFunction`.

### Steps
1. **Store real `HirFunction`s** in the mono table (drop the `Any` erasure) so
   `specialize_function_with_types` can run on them.
2. **Implement `type_subst.spl`**: substitute every
   `HirTypeKind.Named(TypeParam_symbol)` with the concrete `HirType` from the
   binding; recurse through fn signature + body expr/stmt types.
3. **Collect instantiations**: for each `Call` whose callee resolves to a
   generic free fn with one type param, infer `T` from the arg type (the arg's
   already-lowered HIR type, or `type_args[0]` when explicit). Dedup by mangled
   key (`id__i64`, `id__str`).
4. **Clone + specialize**: for each unique instantiation, clone the generic
   `HirFunction`, run substitution, set the mangled name/symbol, insert into the
   owning `HirModule.functions`.
5. **Rewrite call sites** (`40.mono/monomorphize/rewriter.spl`): repoint each
   `Call.callee` to the mangled specialized symbol.
6. **Drop the original generic template** from the module (or mark it
   non-emitted) so no `Named(TypeParam)` survives to MIR.
7. **Relax the HIR free-fn gate** (`declaration_lowering.spl:198`) to defer:
   let a single-type-param free fn through, and move the loud error to a
   **post-Phase-4 sweep** that errors on any `HirFunction` whose `type_params`
   are still non-empty after monomorphization (uninstantiated or unsupported).
   This preserves the "loud on reached-but-unhandled" guarantee while allowing
   the handled tier to succeed.

### Verification per step (dual oracle)
- Oracle: `env -u SIMPLE_BOOTSTRAP bin/simple run <p>.spl`
- Native: `env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH bin/simple native-build --entry <p>.spl -o <o> --clean && <o>`
- Matrix end gate: `sh scripts/check/native-smoke-matrix.shs` → fail=0,
  codegen_fallback_hits=0.

### Risks / guards
- **Live self-interpretation**: native-build interprets `src/compiler/*.spl`
  via the seed; a half-built pass can wedge every native-build. Gate each step
  behind the existing Phase-4 skip and verify the matrix after each.
- **Gate-relaxation ordering**: never relax the HIR gate (step 7) before
  steps 1-6 work end-to-end, or generic fns silently reach MIR again.
- **Interpreter parity**: the interpreter uses a separate dynamic path
  (`10.frontend/core/monomorphize.spl`, `monomorphize_generic_call`); keep it
  untouched. The seed's `bin/simple run` is unaffected by pure-Simple changes.
