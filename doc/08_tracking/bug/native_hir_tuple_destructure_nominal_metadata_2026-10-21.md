# Tuple destructuring loses nominal HIR member metadata

Date: 2026-10-21
Status: source repair and bootstrap compatibility changes authored; unverified.

## Actual failure

The r17-produced `hir_children` object diagnostic failed with six qualified enum
constructor payload mismatches. The retained log is
`build/nogc-hardening/manual-hir-children-build-2.log` in the isolated
`simple-pure-redeploy-20261021` worktree. Its payload trace reports four expected
`named#32` and two expected `named#51` arguments, all with `remembered=none`,
`source=none`, and `mir=present`. Trace line zero does not identify a source line;
diagnostic array indices must not be interpreted as source spans.

The surrounding symbol-binding trace identifies tuple destructuring temporaries
and their `ka`/`kb` projections immediately before these failures. The six
constructor arguments are the two DictLit tuple members, StructLit field value,
HirEnumPayload.Struct field value, HirPatternKind.Struct field value, and
HirPatternPayload.Struct field value. Ordinary `[HirExpr]` indexing succeeds in
the same log with its correct nominal owner. This is a tuple-member provenance
failure, not evidence that all nominal array indexing is broken.

## Production source change

Native tuple GetField projection already preserves its stored MIR representation
and layout markers. Add a separate nominal HIR note from the base's declared
Tuple member when the slot is in range, the current symbol table owns a matching
record/enum declaration, and the destination MIR kind matches the member's
lowered kind. Existing conflicting notes remain intact. This transports declared
type evidence only; it does not decode a value again or bless an erased i64 as
a record. Result/Option wrapper admission retains its separate restrictions.

## Older producer compatibility

Changing compiler source cannot repair r17 while it compiles that source.
The visitor generator therefore emits explicit, schema-derived `HirExpr` or
`HirPattern` bindings between its existing compact tuple destructuring and the
six child-frame constructors. The generated file is updated to match. No type
is inferred from an API spelling; the schema already declares each member.
This is an explicit bootstrap compatibility measure for the recorded compact
form failure, not a claim that a workaround fixes the producer.

The focused fixture `nogc_hir_child_payload_probe.spl` retains its four simple
controls and adds the actual `[(HirExpr, HirExpr)]` indexing/destructuring form.
It imports the real generated child-frame enum, so an old producer can fail
while compiling that dependency before reaching the focused controls. No build
or test was run by the repair author; regeneration equivalence and native
verification remain pending.
