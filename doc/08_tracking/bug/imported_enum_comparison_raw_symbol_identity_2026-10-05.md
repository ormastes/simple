# Imported enum comparison uses raw symbol identity

Status: source-prepared; native verification pending.

The actual pure-Simple producer `27ac2358f22f28c9a43ec3ab47ac3957d5e2b293fc8b44fc52e573512f0c4c69`
compiled both HIR modules of `imported_enum_field_identity`, then rejected three
PacketKind equality/inequality sites during MIR lowering as struct operators.
Its six runtime assertions did not execute. The retained evidence is
`runtime/windows-restart-20261004/scalar-probe-owner-retry1/cranelift/main/compile.log`.

Source audit found a concrete inconsistency: `local_enum_type_id` returned the
raw HIR symbol ID and binary Eq/NotEq required identical IDs. Declaration and
import symbols can differ while naming the same defining module and enum.
The existing `canonical_mir_type_symbol` already normalizes this distinction
for aggregate layout, including physical-path versus dotted owner spellings.

The comparison helper now uses that existing canonical owner after the same
declared-type/registered-enum check. It is a mutating method because canonical
identity allocation updates the lowering's type map. Different owner modules
remain different; ownerless symbols retain their original identities. No
runtime representation, equality ABI, enum discriminant or fallback changes.

Five unit regressions cover same-owner alias equivalence, distinct owners with
the same bare name, ownerless separation, missing/scalar metadata, and an
unregistered named type. All five are UNRUN. The existing six-case imported
field fixture remains the native oracle after producer rebuild. Its failed
log does not expose operand symbol IDs, so the source inconsistency is not yet
proved to be the sole cause of that fixture, nor of the other process/Result
dependency errors. No old compiler retry or qualification claim accompanies
this change.
