# Binary structural equality receives a callable identity instead of a layout key

Status: correction authored; native regression and full qualification pending.

Cycle 4 source: 52eb5d3be92, rebased onto release_phase3 d9e177de79a.
Admitted producer: ef2d27014457e1da10ca5151899503fb491e474ac7b75a7d75cf9db591c34665.
Its 1401-module Phase 2 build, both Hello World sanity modes and custom-operator
native probe passed. The 197-module store closure failed MIR in nine modules,
rejecting EntityUid/SettledAlias operators. No store execution or Phase 3 PASS.

The composed binary_struct_owner helper returned mir_class_identity(owner), a
dotted callable name. Upstream structural fallback passes that name to
struct_structural_eq_supported/lower_struct_structural_eq, whose layout lookup
accepts registered keys or qualified `::` identities. Registering a declaration's
layout and finding its callable method use distinct keys. The dotted name
therefore misses the exact layout even though the declaration is available.
An independent read-only review confirmed the mismatch.

The narrow correction retains declared_struct_layout_key(composite_layout_key(owner))
from the exact HIR declaration. Existing struct_owner_method_key translates the
qualified layout owner to the callable owner for custom methods. It retains
provider isolation and array-element declaration identity validation. No global
normalization or per-record equality workaround is introduced.

The native regression adds a method-less ImportedModulo in another module,
with a distinct prefix/value/marker layout, aliased as PlainRecord by the
consumer. Independently allocated equal values, modulo-different values, first
and last field differences, parameter inequality and array equality/inequality
must all behave correctly. Existing custom modulo equality, scalar arithmetic
and returned-record field checks remain. MIR tests retain demand/eager loading
and require the structural consumer not to call the other provider's dunder.
These authored checks are not PASS before execution.

Evidence: build/native_probe/reconciled-cycle4/ and producer-bound
build/native_probe/{imported-inequality,store-accounting}-cycle4-<producer>/.
The failed candidate's qualification was stopped, proven inactive, and its
caches retained. This correction belongs to user-authorized cycle 5 of 6.

## Failing regression before the correction

The expanded three-module native fixture was compiled with the unchanged
cycle-4 producer. It failed with exit 1: two modules lowered, the consumer
failed on the plain provider's ImportedModulo operators. This is the expected
RED result, saved under
`build/native_probe/imported-inequality-cycle5-red-ef2d27014457e1da10ca5151899503fb491e474ac7b75a7d75cf9db591c34665/`.
The old producer cannot execute the new structural assertions. The corrected
producer is still required for GREEN evidence. Independent read-only review
found no blocking issue in the correction or regression design.
