# Unresolved record receivers ignore their nominal declaration

Related: phase2_subsystem_helper_mir_failures_2026-10-05.
CoreLexer and HashMap typed locals still produced unresolved methods with the
old 2b831559 producer. This separate source gap is relevant but its closure of
those observed errors is not yet runtime-proven.

The unresolved-method path requires struct_value_syms before considering an
instance method. When that representation metadata is missing, its declaration
recovery admitted only Enum; a local with authoritative Named Struct/Class HIR
metadata fell through. Before that point, it could even borrow an unrelated
unique static method with the same leaf name.

The new fallback requires a bound local and real Struct/Class declaration.
Its scalar SymbolTable lookup requires an exact owner-qualified entry, actual
Method symbol kind, canonical declaration name and matching defining module.
It does not use a bare-name registry, unrelated unique static or type-name
fallback. Ownerless declarations require genuinely ownerless matching methods.
Existing representation-backed dispatch and Enum recovery remain unchanged.
Type-valued static receivers are excluded by the runtime-local binding check.

The forced-Unresolved MIR tests deliberately erase receiver layout metadata,
retain its Named declaration and poison the unrelated bare registry. They cover
Struct/Class recovery, same-name and static collisions, forged map/owner/kind
entries, ownerless positive/negative cases, custom get versus Dict builtin, and
unbound static receivers. An authored three-check fixture covers distinct
receiver owners and an Optional initializer. All native/compiled tests UNRUN.

No runtime payload representation, cache identity or release guards change.
Fallback cost is bounded exact symbol-table lookup; timing and peak RSS are
UNRUN and no performance improvement is claimed. Validate using a newly built
producer containing this fix, preserving existing valid caches and failures.
