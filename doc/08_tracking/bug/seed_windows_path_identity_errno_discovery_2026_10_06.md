# Seed Windows path identity errno discovery

Bug: seed_windows_path_identity_errno_discovery_2026_10_06
Status: scoped workaround candidate; native positive verification pending.
Canonical bug DB registration pending through its owner API.

Pinned seed283f failed the 3607 Phase2 build before module compilation:
path_identity_abi.spl line20 unsupported @when condition. CFEC/native exited1
with complete quiescent RSS receipt and no compiler output. Adding Windows
runtime object caching introduced the path_identity dependency exposing this
existing seed syntax limitation. The seed preprocessor accepts only
@when(os="windows"): and rejects other OS conditions even inside inactive
branches; merely wrapping the errno chain in another Windows branch cannot fix
it. The seed remains unchanged.

The workaround moves the unchanged POSIX errno conditional chain to a leaf
module imported only by the existing non-Windows branch. Windows retains its
original zero errno-address behavior. malloc/free/realpath/readlink and Windows
ABI declarations, annotations and exports remain with their original owner.
path_errno_address is exported by the original facade on every OS. Linux,
FreeBSD, macOS and fallback provider bodies are unchanged, including ordering.
No checker, path identity guard or fail-closed policy is disabled.

Evidence: four host tests compiled the exact strip_os_when_blocks function
extracted from current pinned-source cfg_strip.rs. They reproduce original
line20 failure, verify Windows discovery excludes the POSIX module import,
verify POSIX import/export ownership, and prove moved provider bytes identical.
All four passed. This does not prove the already-built seed binary's complete
native pipeline compatibility. The actual negative seed reproduction is the
3607 Phase2 attempt; native positive fixture execution remains UNRUN.

Regression: build test/fixtures/compiler/windows_path_identity_errno_branch/main.spl
with the unchanged Windows seed, --entry-closure and existing std source roots;
it must link and return0 with the precise Windows errno-branch PASS line.
Then resume cached Phase2 attempt2. No unchanged full build was retried.
Retire the import workaround only after an applied seed preprocessor fix
supports the other OS conditions and native discovery qualification passes.

Discovery scope review: native_project/discovery.rs810-817 dispatches to entry
closure when requested;845-926 starts a queue from the sole entry and strips
OS branches before parsing. Dependency extraction follows at1118. However,
reachable __init__.spl bare exports trigger nonrecursive read_dir sibling
preprocessing at991 and1097, so a same-directory POSIX file is insufficient.
The corrected leaf is io/_PathIdentityPosix/errno_abi.spl, with no initializer.
It is not a direct .spl sibling; the Windows-stripped facade contains no import
that can queue it. POSIX retains the explicit leaf import and original export.
Broad --source src/lib supplies resolver roots, not a forced full scan, under
--entry-closure. This is exact source-callgraph evidence, not native-positive
execution.
