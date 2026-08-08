# Loader settlement export updates were non-transactional

- **Status:** SOURCE-FIXED; fresh Stage 4 execution pending
- **Found:** 2026-07-23 during bottom-up loader hardening
- **Component:** `compiler.loader.settlement`

## Bug

`SettlementContainer.set_exports` wrote the module's new export list before
registering it with `SettlementLinker`, then logged and ignored duplicate
strong-symbol errors. A rejected update therefore returned `Ok`, could leave
part of the new linker table installed, and made module metadata disagree with
symbol resolution. Replacing an export list also left removed names stale.

## Fix

The container now rebuilds a candidate export table from authoritative module
entries in module order. It substitutes the requested module's candidate list,
propagates the first linker error, and commits both module metadata and linker
exports only after the full replay succeeds. Replaying all modules also restores
weak symbols previously shadowed by the replaced set. Replay deduplicates stale
module-order entries after remove/re-add and retains fallback/JIT exports that
are not owned by a registered settlement module.

The focused contract covers duplicate rollback, stale-name removal, replacement,
weak-to-strong precedence, remove/re-add, and fallback preservation. Exact fresh Stage 4 execution remains pending
because the deployed pure-Simple artifact is still the bootstrap-only compiler.
