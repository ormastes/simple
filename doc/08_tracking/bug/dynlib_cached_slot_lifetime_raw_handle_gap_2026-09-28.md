# Cached SFFI slots and raw handle ownership are not yet unified

**Status:** Open. The `fix/sffi-cached-slot-lifetime-20260928` worktree is an
unpublished candidate, not release evidence.

## Evidence

`DynI64FnSlot` retains a raw function pointer after `DynLib.close()` unloads its
provider. A copied or retained slot can therefore call unmapped code. The
candidate introduces a revocable mapping identity and defers `dlclose` until
admitted calls finish, but the existing raw API still exposes `DynLib.handle`.

`chromium_reference_oracle_sffi.spl` and `chrome_render_module_sffi.spl` obtain
that handle through `DynLib.load()`, then close it directly with `spl_dlclose`.
`wffi_into_bytes_spec.spl` does the same. Those closes bypass the candidate
owner, leaving an entry that appears live after the native mapping is gone.
The GPU modules also retain raw function pointers in their own handle structs.
The candidate must not be published until those ownership routes are made
explicit and checked together.

The candidate's owner takes a mutex on every cached-slot call. The selected
environment variant NFR-003 forbids a lifecycle lock in dense provider batch
dispatch and limits its overhead to 2% against a direct reference batch call.
The existing `native_callable_owner_v1` also takes a mutex on each native
invocation; it is a correctness staging point, not NFR evidence. No latency,
allocation, or RSS comparison for the candidate has been run.

## Acceptance

1. One owner closes each mapping exactly once, including raw GPU success and
   failure paths, while stale slots and stale aliases return a typed refusal.
2. An admitted call survives concurrent retirement and the final use closes
   the mapping. New calls fail after retirement.
3. Versioned and convention loader caches never return retired entries.
4. A source-matched pure-Simple runtime runs the native fixture and lifecycle
   tests. The checked dispatch meets NFR-003 on its named batch fixture with
   no per-element lifecycle lock or allocation.
