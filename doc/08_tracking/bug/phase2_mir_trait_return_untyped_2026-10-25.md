# Phase 2 MIR: trait-call and generic-call results lose their type (2026-10-25)

## Symptom
Phase-ladder run 40157771919, linux-riscv64 rung 2: the pure-Simple phase-1
compiler (fresh, seed-built from `b60d965ab`) builds phase 2 through HIR and
monomorphization (no OOM), then MIR lowering fails 13 of 1518 modules, 129
errors. Largest groups:

| file | error | cause |
|---|---|---|
| `70.backend/linker/obj_taker.spl` | `unresolved method call: is_err/unwrap/unwrap_err` | result of a call through trait `SmfReader` |
| `20.hir/hir_codec_support.spl` | `bare variant 'Ok' is ambiguous` | `match` on a generic `enum_wire_*` call |
| `70.backend/backend/backend_helpers.spl`, `backend_api.spl` | `bare variant 'Ok' is ambiguous` | result of `Codegen.compile_module` (trait) |
| `40.mono/instantiation.spl` | `unresolved method call: is_err` | result of `CompilationContext.compile_template` |
| `lib/.../gzip/inflate.spl` | `tagged Any addition ...` | untyped params of `deflate_block_parse` |
| `lib/.../gzip/compress.spl` | `unresolved method call: len` | `var x: [u8]` assigned from untyped-param fns |

The trait method's declared return type is not attached to the call result,
and a bare `Ok`/`Err` arm then matches several enums that declare `Ok`.

## Workaround (this change)
Typed locals at each call site (`val r: Result<..> = trait_call(...)`) and
typed parameters on `deflate_block_parse`. No runtime cost.

## Open
- Propagate trait/generic call return types in MIR lowering so the
  annotations are unnecessary.
- `gzip/compress.spl:45,86` still unexplained (declared `[u8]` local).
- `40.mono/monomorphize/hir_subst/body_subst.spl:224,242` (`Tuple`/`Struct`
  ambiguous) was reworked upstream in 2dbf93939d2; re-check on the next run.
- Macro files (`macro_source_from_parse_v1.spl` etc.) fixed upstream in
  03b365380f0.
