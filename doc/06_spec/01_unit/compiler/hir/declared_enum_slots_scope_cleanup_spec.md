# Declared enum slot scope cleanup

Status: AUTHORED_UNRUN. Source/API review only; no qualified self-hosted CLI was
used to compile or execute these scenarios. This manual mirrors
`test/01_unit/compiler/hir/declared_enum_slots_scope_cleanup_spec.spl`.

| Scenario | Real setup and oracle |
|---|---|
| Detach registered payload metadata before reclamation | Parse a named enum before opening a real transient scope; create its slot graph through `register_declared_pattern_enum_slots` inside the scope. Require actual field metadata, pause, call the common `begin_module`, and capture that the slot map is empty before ending the scope. Verify idle scope state and the preexisting retained phase memo afterward. |
| Remove keys before numeric symbol reuse | Parse/register the enum through the same production owner. Reset the symbol table using `begin_module`, define another enum, prove its numeric ID is reused, and require that the old payload key is absent. |

The first scenario records only a scalar detachment result before reclamation;
it never reads the old slot graph after scope end. Removing the new reset makes
the pre-reclamation empty-map assertion fail deterministically, without relying
on allocator churn or a crash. This negative control is source-derived and has
not been executed. Both cases use the common reset without the archive-only
caller's extra clear.

No RSS improvement, r1 archive publication fix, cache-off retained-path cleanup,
or historical SIGSEGV qualification is claimed. The retained memo sentinel
checks that this change does not indiscriminately clear phase state; it does
not certify every retained root.
