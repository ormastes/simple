# Loader settlement import replacement and removal left stale indexes

- **Status:** SOURCE-FIXED; fresh Stage 4 execution pending
- **Found:** 2026-07-23 during bottom-up loader hardening
- **Component:** `compiler.loader.settlement`

## Bugs

`set_imports` appended new references to `SettlementLinker.imports` after
replacing `ModuleEntry.imports`. Repeating or replacing a module's imports
therefore retained old references and duplicated unresolved diagnostics.

`remove_module` deleted only the container entry and one side of dependency
edges. Its exports, import references, linker module ID, dependent-side edges,
and cached load order survived. A later link could resolve against a removed
provider, and remove/re-add accumulated module IDs.

## Fix

Import updates now stage a replacement map by `ImportRef.from_module`, preserve
other owners, then atomically commit the module entry and linker map. Removal
first clears the module's authoritative exports/imports through those canonical
owners, removes both graph-edge directions and linker ordering, invalidates the
cached order and resolution counters, and demotes remaining linked entries to
loaded until the next successful link.

The linker now retains fallback/JIT exports separately from its active export
view. A same-name module export may shadow a fallback temporarily; replacement
or removal rebuilds the active view and reveals the retained fallback again.

The focused settlement contract covers stale/duplicate import replacement,
unresolved counts, full provider removal, unresolved relink, clean re-add, and
same-name fallback restoration.
Execution with an exact fresh Stage 4 binary remains pending.
