# Zero-byte tracked `.spl` files under `src/` — salvage/wipe residue audit

**Date:** 2026-08-18
**Status:** TRIAGED — one real truncation found, five benign; no data lost
**Related:** REBASE91 salvage triage (`e9e22a1230f`), tree-wipe restore `ae55a746719`

## Why this audit

`src/app/debug/remote/types.spl` was found at **0 bytes** and
`src/lib/nogc_async_mut/debug/remote/types.spl` **absent**, both named in the
declaration list of `test/01_unit/lib/debug_config_literal_fields_spec.spl`.
This repo has a documented history of tree wipes and of a REBASE91 salvage that
silently dropped landed fixes, so emptiness-in-place is treated as a loss
signal, not as a deletion.

## Full 0-byte tracked `.spl` census

    find src -name '*.spl' -size 0 -not -path '*/vendor/*'

**7 files. Full list:**

| path | ever non-empty? | verdict |
|---|---|---|
| `src/app/debug/remote/types.spl` | **YES — 5311 bytes at `ae55a746719`** | **REAL TRUNCATION** (see below) |
| `src/compiler/99.loader/resource_lifecycle.spl` | no | benign shadow |
| `src/compiler/99.loader/smf_cache_manager.spl` | no | benign shadow |
| `src/compiler/99.loader/generation_sweeper.spl` | no | benign shadow |
| `src/compiler/99.loader/mod.spl` | no | benign shadow |
| `src/compiler/99.loader/module_loader_lib_support.spl` | no | benign shadow |
| `src/compiler/test_pkg/mod.spl` | no (0 bytes at `v0.9.1` too) | benign placeholder |

### The five `99.loader/*` shadows are NOT losses

Each has a same-named, non-empty sibling one level down in
`src/compiler/99.loader/loader/`, and that is what the importers resolve to
(`loader/module_loader.spl:29` `use .resource_lifecycle`, `:36`
`use .smf_cache_manager`; `loader/resource_lifecycle.spl:13-14`;
`loader/module_loader_services.spl:13-14` — all relative-`.` imports resolved
inside `loader/`):

    loader/resource_lifecycle.spl        12230 B
    loader/module_loader_lib_support.spl  9715 B
    loader/generation_sweeper.spl         5242 B
    loader/smf_cache_manager.spl          2858 B
    loader/mod.spl                          537 B

The top-level 0-byte copies have **never** carried content in any reachable
commit (checked at `v0.9.1` and at `ae55a746719`: absent / 0). They are stale
scaffold, not truncated files. `src/compiler/test_pkg/mod.spl` is likewise
0 bytes as far back as `v0.9.1`.

## The one real finding: `src/app/debug/remote/types.spl`

- **5311 bytes** at `ae55a746719`; **0 bytes** from `c4fa74c1b16`
  *"chore(salvage): 16 net-new files from commits that could not be
  cherry-picked"* — the salvage wrote it as an empty blob (`| 0` in that
  commit's diffstat, the only 0-line entry among 16 files). Classic
  delete-by-emptiness: the file was neither kept nor removed.
- Its recovered content is **byte-identical to
  `src/lib/nogc_sync_mut/debug/remote/types.spl`** except for one trailing
  `export Architecture, HaltReason, DebugError, Endianness, DebugConfig` line
  (`diff` → 2 added lines, nothing removed, nothing changed).
- **Zero importers.** No `use`/`import` of `app.debug.remote.types` exists
  anywhere in `src/` or `test/`. Its own directory siblings
  (`src/app/debug/remote/backend.spl:4`, `backend_generic.spl:6`) already import
  `std.nogc_sync_mut.debug.remote.types`.

### It must NOT be resurrected

Restoring it would re-create a third co-compilable declaration of
`DebugConfig`/`Architecture`/`Endianness`/`HaltReason`/`DebugError`. That is
precisely the hazard commit `36a5a0e8291` *"fix(lib): collapse two
byte-identical async-lane debug/remote duplicates"* removed: the interpreter's
class registry is keyed on the bare class name across co-compiled modules, so a
cross-module duplicate mis-dispatches method bodies. That commit **deliberately
deleted** `src/lib/nogc_async_mut/debug/remote/types.spl` (the "absent" file in
this report — it is a correct, documented deletion, not a loss) and repointed
its 23 importers at the canonical `std.nogc_sync_mut` module.
`src/app/debug/remote/types.spl` is the same duplicate on the app lane and
should reach the same terminal state.

### Recommendation (needs owner approval — not done by this lane)

`git rm src/app/debug/remote/types.spl`, completing `36a5a0e8291`'s collapse.
No importer changes are required (there are none). This lane deliberately did
**not** delete it: removing product source was not authorised, and the 0-byte
file is inert — it declares nothing, so it cannot mis-dispatch while it sits
there. The guard spec
`test/01_unit/lib/debug_config_literal_fields_spec.spl` already documents both
paths' status in its declaration list and passes against the current tree.

## Conclusion

No content was lost. The 0-byte census is 1 mis-salvaged duplicate (recoverable
from `ae55a746719`, but should be deleted rather than restored) and 6 files that
never had content.
