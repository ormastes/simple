# Compiler sources pass `nil` into non-optional HIR enum payload slots

- **Date:** 2026-10-20
- **Status:** open
- **Area:** 20.hir / 50.mir (Phase-3 self-lowering)
- **Found by:** follow-up to PR #3924 (Opus post-merge review)

## Problem

PR #3924 made MIR accept `nil` in every class/struct/enum payload slot. It did
this so that the compiler's own sentinel uses would lower. That is not proven:
a later `match` or field read on the nil can miscompile or crash natively. The
follow-up now accepts `nil` only in a declared optional slot (`T?`). A nil into
a non-optional class/struct/enum slot is a MIR error:

```
enum construction 'E.V': payload type mismatch at N: nil into non-optional
payload slot (declared 'T'); declare it 'T?' if absence is valid
```

The compiler's own HIR lowering still passes `nil` into two such slots, so
Phase-3 self-lowering will report these again, and loudly:

| Slot (declared non-optional) | Sites |
|---|---|
| `HirStmtKind.Let(symbol, type_: HirType, init)` (`hir_definitions.spl:800`) | `20.hir/hir_lowering/statements.spl:343,376,449,488,528,839`; `20.hir/hir_lowering/_Expressions/match_desugaring.spl:34,460,947`; `50.mir/_MirLowering/module_lowering.spl:3764` |
| `HirExprKind.DictLit(entries, key_type: HirType, value_type: HirType?)` (`hir_definitions.spl:579`) | `20.hir/hir_lowering/_Expressions/expression_core.spl:818` |

Readers already treat both as nullable: `type_ != nil` and `type_ ?? fallback`
in `mir_lowering_stmts.spl:176,181` and `array_move/mir_array_move.spl:197,203`,
and `annotated_key != nil` in `enum_constructor_payload.spl`.

## Fix

Declare the slots nullable: `type_: HirType?` and `key_type: HirType?`. Then
regenerate `20.hir/generated/hir_codec.spl` with its generator
(`scripts/check/check-hir-codec-complete.shs`). The follow-up lane did not make
this change, because nobody could check its effect on readers that pass
`type_` straight into a `HirType` parameter
(`40.mono/monomorphize/type_subst.spl:319`, `hir_subst/body_subst.spl:268`,
`monomorphize_integration.spl:2212,2725`). That needs a Phase-3 self-lowering
run, and bootstrap runs had priority.

## Related open gaps in the same lane (native closure decode, #3923 follow-up)

The fix for the thread spawn crash makes the user-VA ceiling correct for
x86_64 and aarch64. It also tests "is code" against executable `PT_LOAD`
segments. Two gaps are still open:

- **riscv64 Sv39:** user space ends below 2^38, and the PIE base is about
  `0x2a_aaaa_a000`. An `addr << 3` word (about 2^40) still sits under the
  47-bit ceiling, so it is read as a raw address. This is the same crash
  class. Fix: add a riscv64 ceiling (`#if defined(__riscv)` / `cfg`) once
  the Sv39 vs Sv48 mode is known at runtime, or make the encoding explicit.
- **macOS:** the "is code" test falls back to `dladdr`, which also resolves
  data addresses. Fix: test the `__TEXT` segment range (`getsegbyname`).
- **Long term:** the shifted (`addr << 3`) closure word comes from seed
  codegen. If codegen always emits the direct-function record, which carries
  an explicit marker, the ceiling heuristic can be deleted.

## Update 2026-10-20: nil only in unsafe (work/nil-only-unsafe)

Language rule: `nil` may be used only inside `unsafe`. Safe code spells
absence `None`. MIR now also rejects nil in a declared optional (`T?`) payload
slot outside an `unsafe:` / `danger:` block:

```
enum construction 'E.V': payload type mismatch at N: nil outside unsafe into
optional payload slot (declared 'T?'); use None
```

`None` is accepted there. Inside `unsafe:` nil is accepted into a `T?` slot
only; nil into a non-optional slot stays rejected inside unsafe too. Only
block-level unsafe counts: `@unsafe` on a fn is parser metadata
(`UNSAFE_ANNOTATIONS`) and never reaches HIR/MIR.

Representation: natively, `None` lowers to `rt_enum_new(OPTION, 1, 0)`, a heap
object, while `nil` is the word 3. `rt_is_none` treats both as absent, but
`rt_native_eq(None, nil)` returns 0. The seed interpreter treats them as
equal. So builtin `None` in an enum payload slot now lowers to the same nil
word: in declared `T?` slots, and in untyped constructions of a non-generic
owner. Generic owners keep the Option object. That keeps the 219 converted
sites identical on the native lane. Converting nil to
None in struct fields or plain variables is NOT representation-preserving yet.

### Still open: the non-optional sites

The Fix above (`type_: HirType?`, `key_type: HirType?`) does not work as
written: MIR rejects a bare `T` value in a `T?` payload slot (measured:
`OS.V(x)` with `x: Node` -> "payload type mismatch at 0"). Every annotated
`HirStmtKind.Let(sym, t, init)` would then need `Some(t)`, and that box is the
measured native SIGSEGV recorded at `statements.spl:580-600`.

Sites, all already rejected by #3931 and untouched by this change:

| Slot | Sites |
|---|---|
| `HirStmtKind.Let.type_: HirType` | `20.hir/hir_lowering/statements.spl:343,376,449,488,528,839`, `_Expressions/match_desugaring.spl:34,460,947` (`module_lowering.spl:3764` passes a nil-valued variable, not a `nil` literal, so MIR does not see it) |
| `HirStmtKind.Assign.op: HirAssignOp` (missed above) | `statements.spl:98,479` |
| `HirExprKind.DictLit.key_type: HirType` | `_Expressions/expression_core.spl:818` |
| `IntroducedSymbol.Variable` (src/app, not compiler closure) | `src/app/dap/protocol.spl:174` |

Candidate fix that needs neither nil nor a box (owner decision): an
`HirTypeKind.Infer` sentinel for an unannotated `Let.type_` / unannotated
`DictLit.key_type` (the flat AST already uses a present Infer type for "no
annotation", `statements.spl:574`), and a plain-assign variant for
`HirAssignOp`. Every reader that tests `type_ != nil` / `?? fallback` must
switch to the sentinel test in the same change.
