# Generic collector copied SymbolId lookup

Status: source candidate; tests AUTHORED_UNRUN. No specialization or promotion runtime success claimed.

The captured 9ce producer mono source (SHA256 14ce1cc87629a07e0ceffb071592ef67baa8f3437eec1f8f22826250f75bcfd3) iterates function keys and looks up each copied aggregate SymbolId again. Its own sorted_function_indices documentation explains that native erased dictionaries compare aggregate keys by identity and copied keys can lose the retained payload. The collector nil guard then silently skips such an entry.

The final inferred promotion diagnostic returned generics=none before root traversal. Its roots=0 is an early-return profile constant, not independent evidence of missing root functions. Both inferred and explicit source calls link-failed with an undefined ordinary transient_promote wrapper. These facts support this collector defect but do not prove that correcting it alone resolves promotion; extern generic binder transport remains a separate known defect.

The correction retains functions.values() and addresses the array by scalar index. A typed HirFunction binding preserves symbol/name registration; collection order is not sorted or otherwise changed. Generic impl and class-static owner registration remain unchanged. No malformed-template flag invariant is introduced because owner-generic methods legitimately have no function-local binders.

Existing SIMPLE_MONO_DIAG enables only a bounded provider summary and at most32 entry descriptions for lib.nogc_sync_mut.sffi.transient. No semantic flag or new schema is added. The regression reparses real declarations and rekeys their function map with separately constructed SymbolIds, testing both template body modes and owner binder controls. The native fixture checks standalone generic, owner method/static and ordinary call results.

No compiler execution, producer rebuild, or fourth unchanged inferred diagnostic is authorized by this source packet. A changed producer and real promotion lifetime fixture remain required for qualification.
