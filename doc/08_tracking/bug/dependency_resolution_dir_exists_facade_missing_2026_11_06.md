# Dependency resolver imports an unresolved directory-probe facade

Canonical ID: `dependency_resolution_dir_exists_facade_missing_2026_11_06`.
Severity: P1. Status: source repair implemented; executable verification pending.

Linux Phase Ladder run42208359530, job127860566362 failed the Phase2 HIR
boundary at source pin `bbfe33dd9f1d1c0007f79788b5f8ff67b2fddbd0`:

    unresolved name: dir_exists
    src/compiler/00.common/dependency/resolution.spl:117:31

The closure contained1593 modules. This is a real failed compiler boundary,
not a successful Phase2 receipt. Exact producer/build authority is being
recovered from the CI artifacts; this report does not infer qualification from
a filename, stage label or linked binary.

The defect remains in release source
`587116dc5d1fb9a3f53270d6b10de2fc56db423a`.
`resolve_segment_with_numbering` imports `file_exists` and `dir_exists` from
`std.io`. The actual diagnostic identifies the selected facade as
`lib.nogc_async_mut.io`: it exports the directory-probe name but has no
declaration or resolvable explicit forwarding route for it. Its self-alias
`use std.io.*` imports do not establish that missing provider.

The resolver now imports both operations through the existing
`std.io_runtime` facade. That facade explicitly forwards them to the standard
runtime owner and is already used for the same checks by compiler source-root
handoff and cache modules. This is an importer correction, not a global
variant-selection pin or an expansion of the broken I/O facade. Resolver
control flow, return values and the unimplemented numbered-directory fallback
remain unchanged.

The regression fixture is
`test/fixtures/compiler/dependency_resolution_filesystem_probe/main.spl`.
It imports and calls the actual resolver owner, requires real directory/file
probes to distinguish the fixture directory, its source file and an absent
path, then checks existing directory/file/missing compatibility results. Run
from the repository root. Required native stdout is exactly:

    dependency resolution filesystem probes OK

Its central regression is successful self-hosted name binding and native
compilation of the actual owner; a seed's flat-name behavior is not a valid
substitute. Native compile/run, the original1593-module HIR build and required
core/MCP gates are **UNRUN** for this repair. No bootstrap restart or broader
Phase2/Stage3 completion is claimed.
