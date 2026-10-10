# Mono specialization symbol id collides with a non-function symbol

Status: open. Found while proving the fn-typed parameter ABI (commit
"keep fn-type annotation shapes so generic visitors monomorphize").

## Symptom

For

```simple
fn walk<C>(n: i64, ctx: C, f: fn(i64, C) -> C) -> C: ...
fn add(n: i64, c: i64) -> i64: c + n
fn main() -> i64: walk<i64>(3, 0, add)
```

monomorphization creates one specialization, HIR names it `walk$i64`, and
MIR names it `walker_abi.C`. LLVM IR then defines `@walker_abi.C` and the
recursive call and the `main` call both target `@walker_abi.C`. The program
is still internally consistent (it links and runs), but the symbol name is
wrong. Two specializations that land on aliasing ids, or one whose alias
is another function, would break the link or call the wrong code.

## Cause

`src/compiler/40.mono/monomorphize_integration.spl`:

- lines ~255-259 set `next_symbol` to (largest **function** symbol id) + 1;
- lines ~381-387 hand that id to the specialization (`SymbolId.new(sym)`).

The module `SymbolTable` also holds non-function symbols (here the type
parameter `C`), and those can have higher ids. MIR names a function through
`provider_callable_symbol_name(fn_.symbol, ...)`
(`50.mir/_MirLowering/function_lowering.spl:404`), which resolves the id in
the symbol table and so finds `C`.

## Fix direction

Allocate specialization ids past the symbol table's maximum id (or register
the specialization in the table) instead of past the largest function id.

## Evidence

`test/01_unit/compiler/backend/generic_walker_fn_param_abi_spec.spl` finds
the walker by arity instead of name for this reason. A debug driver over
the same source printed `hir fn key=... name=walk$i64` and
`fn walker_abi.C params=[i64, i64, funcptr/2]`.

## Mitigation (2026-10-10, work/rel-robust-post-mono-verify-20261010)

- Allocator: `collect_generics` now seeds `next_symbol` past every module's
  `symbols.next_symbol_id` as well as past its function ids, so a
  specialization can no longer land on a type parameter's or local's id.
  A fixed high-range base (branch `work/rel-stage2-generic-class-params-20261010`,
  `MONO_SYMBOL_BASE`) satisfies the same invariant; the two compose.
- Verifier (`40.mono/verify/post_mono_verify.spl`), default-on, every profile
  that runs the post-mono verifier:
  - **E-MONO-035** specialization id bound by a module table to another
    symbol, or below the table's next free id; also at CALL sites when the
    CALLER's table binds the id (`walk$i64` -> `walker_abi.C` shape), with
    the call-site span;
  - **E-MONO-036** a call still binding a generic template with no emitted
    definition (pruned after specialization), call-site span;
  - **E-MONO-037** duplicate specialization key across the closure, plus
    `post_mono_specialization_manifest` (sorted) for cross-run determinism;
  - **E-MONO-038** `post_mono_archive_admission_v1`: a module lowered in an
    archive-producing lane must have `MirLowering.devirtualized_calls` delta 0
    (verifier twin of `driver_trait_devirtualization_allowed_v1`). Applied to
    all three driver-owned lowering instances (direct, bootstrap-fixed,
    fallback); the fallback instance never sets `trait_impl_closure_complete`
    so it cannot devirtualize today — the check there is defense in depth.
  - E-MONO-036 keys templates by `<module>.<name>` and skips `is_method`
    templates: a generic class's method is `is_generic_template` under its
    bare name, and keying it mis-read a cross-module call to a free function
    of the same name (`std.nogc_async_mut.async_embedded` `ready`/`pending`).
- Spec: `test/01_unit/compiler/mono/verify/post_mono_symbol_identity_spec.spl`
  (18 examples). The real-pass walker case fails with E-MONO-035 before the
  allocator seed and passes after. The by-arity lookup in
  `generic_walker_fn_param_abi_spec.spl` can now be replaced by name.
