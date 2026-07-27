# Bug: nil Dict receiver — `.get()` returns phantom Some while `.len()` returns -1 (stub Module, stage-4 segfault lineage)

**Date:** 2026-07-27
**Status:** Open
**Area:** native codegen (Dict nil-receiver methods) + Rust seed (HirLowering field-type inference)

## Summary

During stage-4 bootstrap, `HirLowering.register_imported_symbol` operates on a
stub `Module` whose dict fields (e.g. `imported_const_decls`) were never
initialized. The seed nil-fills omitted struct-init fields, so the field holds
nil. Two root defects:

1. **Native codegen, phantom Some:** `.get(key)` on the nil Dict receiver
   returns a phantom non-nil Option (a "Some" wrapping garbage) while `.len()`
   on the same receiver returns -1. Downstream code trusts the phantom Some and
   dereferences garbage — the stage-4 bootstrap segfault lineage. The
   fail-closed contract is: `.get()` on a nil receiver must return nil, and
   `.len()`/`.get()` must agree (len() <= 0 implies get() -> nil).

2. **Seed field-type inference, hair-trigger control-flow sensitivity:** the
   seed's field-type inference in `HirLowering.register_imported_symbol` is
   sensitive to the guard's control-flow shape — four distinct guard shapes
   each broke with `cannot infer field type ... imported_const_decls`, making
   it impossible to guard the nil receiver at the call site without tripping
   inference.

## Repro spec

`test/01_unit/compiler/hir/nil_dict_receiver_phantom_option_spec.spl` — a
deliberately RED spec pinning the desired fail-closed contract (defect 1):

- `it "nil dict receiver returns nil from get, never a phantom value"` —
  `.get("k")` on a nil-filled Dict field must be nil.
- `it "len and get agree on a nil dict receiver: non-positive len implies nil
  get"` — if `.len() <= 0` then `.get()` must be nil.

The spec constructs a `StubModule` with an omitted (hence nil-filled)
`imported_const_decls: Dict<text, i64>` field, mirroring how the compiler hits
the receiver. It is EXPECTED RED under native codegen until the nil-receiver
fix lands; per repo convention for filed defects it stays visibly red (no
`skip()` — precedent: `rv32_trap_completeness_spec.spl`). Interpreter
semantics may differ from native; the spec's value is as the native-contract
pin.

## Refined root cause (SIMPLE_BOOTSTRAP_DIAG run)

The "stub" modules are **header-only registry entries**: files OUTSIDE the
entry closure get parsed for name/imports/exports only, so their decl dicts
are nil while `.name`, `.imports`, `.exports` read correctly. Diag evidence —
the swept siblings themselves are partial:

```
[reexport-chase] mod=std.nogc_sync_mut.io.pipe wanted=Read ... found=true
                 mname=src/std/nogc_sync_mut/io/pipe.spl fns=-1
```

`resolve_package_sibling_symbols` sweeps ALL `modules_by_name` keys under the
package prefix — including partial entries — and the facade-glob chase then
walks the partial module's imports into `std.io.traits` (also partial), where
the trait arm unwraps the phantom.

## Mitigation (landed 2026-07-27)

Skip partial modules in the sibling sweep
(`resolve_package_sibling_symbols`): register a sibling's glob symbols only
when `(sibling_mod ?? module).functions.len() >= 0`. A partial sibling
contributes no compiled symbols, so this is semantically clean — packages'
bare cross-file calls only ever resolve against closure members.
`register_imported_symbol` stays byte-pristine.

Why not guard in `register_imported_symbol`: FOUR shapes all break the seed
build with `hir: Unsupported feature: cannot infer field type ... field
'imported_const_decls'` (a pristine-file control build compiles clean, so the
coupling is real, not cache poisoning):
1. `var ... = nil` + conditional assign on all six lookups
2. single-line if-expression initializers on all six
3. single-line if-expression on the trait lookup alone (fresh cache)
4. `traits.len() > 0` added to the elif condition, and separately as a
   nested if inside the arm around `lower_trait` (fresh caches)
Meanwhile an added `eprint` statement at existing nesting compiled fine. The
seed's field-type inference for `imported_const_decls` is hair-trigger
sensitive to control-flow shape in this one function — that fragility
deserves its own fix.

The phantom-Some hazard remains for any OTHER path that hands a partial
module to `register_imported_symbol` (direct imports of out-of-closure
modules, glob-import path); the real fix below covers those.

## Real fix

- Make native nil-receiver `Dict.get` return nil (align with `.len()`'s
  defined -1 behavior), with a deliberate-red spec on a nil-dict receiver.
- Root-cause why the `std.io.traits` Module object is a stub with nil dicts at
  sweep time (alias-key registration path in `resolve_module_key`?).
- Harden seed field-type inference so a guarded initializer among sibling
  `val`s does not detach `imported_const_decls` from its inferred type.

## Repro

Stage-4 native-build of `src/app/cli/main.spl` (full closure, llvm backend) at
main ≥ d07208d1c4f without the mitigation; crash at HIR module 32.

## Related

- `doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-27.md` (Lane H)
- `reference_jit_option_i64_value3_none_collision` (memory)
- Trap D note in `module_lowering.spl` `lower_parser_module_unstub`

## Second site: direct-import path (2026-07-27, same day)

With the sibling-sweep guard in place, the stage-4 repro cleared the original
crash point (env_ops.spl, HIR module 32) and 69 modules, then segfaulted in
`resolve_import_symbols` for `src/lib/nogc_async_mut/database/test.spl` — the
same phantom-Some family via `register_imported_symbol`'s six decl-dict
`.get()` lookups on a header-only imported module. Second guard: early-return
at the top of `register_imported_symbol` when
`imported_mod.functions.len() < 0`, falling through only to the re-export
chase (header parsing does populate imports/exports). This gate covers every
caller (direct import, glob, sibling sweep, re-export recursion).
