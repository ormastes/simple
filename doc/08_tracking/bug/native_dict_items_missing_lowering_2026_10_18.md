# Native Dict.items has no method lowering

## Observed failure

The admitted pure-Simple d85dd53b producer rejects a dictionary `.items()`
control during MIR lowering as an unresolved method. The corresponding direct
`for (key, value) in dict` control succeeds. This is independent of the open
record-key hashing defect: copying a record key before a second dictionary
lookup may miss even when the original live key/value slot is intact.

## Repair

Add `.items()` to the existing dictionary receiver probe and dispatch only on
a proven dictionary. Reuse a prelowered receiver, reject arguments, and recover
key/value types from local MIR and declared HIR, including mutable references.
Unknown field representations fail closed instead of guessing integer slots.
The method uses `rt_dict_entries` to snapshot paired slots, then the existing
`builtin_runtime_tuples_to_native` conversion. Direct dictionary pair loops
call the same helper while retaining their existing field-type derivation.

The result keeps runtime array/value markers and its native tuple element
type. Text uses the established bootstrap text representation; nominal fields
retain their own MIR types. No second hash lookup, runtime change, codec
change, ordering guarantee, or `.entries()` alias is introduced.

## Scope and validation

Isolated branch `work/dict-items-native-lowering-20261018`, base
`99e74521fb6af600bacbf99a82a2380b906be64d`. Three production MIR files;
the live 323d candidate and sibling codec patch remain separate.

`test/01_unit/compiler/mir/dict_items_lowering_spec.spl` lowers real source to
MIR and checks paired-slot calls, native tuple types, nominal field access,
mutable-reference/field receivers, single receiver evaluation, invalid arity,
ordinary custom/static dispatch, and preservation of direct dictionary loops.

`test/fixtures/compiler/native_dict_items.spl` checks text/integer and
boolean/float associations, record key/value fields, empty dictionaries,
receiver side effects, mutable-reference calls, direct loops and custom
methods. Success is exit zero plus `DICT_ITEMS_NATIVE_PASS`; iteration order
is deliberately irrelevant. Record keys are not re-looked-up in the fixture.

Dynamic checks are **UNRUN** pending review and a patched compiler. The existing
producer's passing direct-loop control does not validate this new lowering.
Both native backends and the actual-MIR regression remain required; no whole
suite or release qualification is claimed.
