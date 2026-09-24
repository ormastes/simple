# macOS Phase 2: nested selective-import alias links to a bare symbol

Status: fix proposed; Stage 2 producer rebuild and full Phase 2 verification pending.

The 2026-09-23 full-CLI Phase 2 build from source `70748fd0` failed at the
macOS linker. In `src/compiler/99.loader/loader/smf_mmap_native.spl`, calls to
`owner_munmap` and related `owner_*` aliases emitted undefined bare symbols.
The archive already defined their imported owners as
`_compiler__loader__smf_mmap_native__native_*`; this was not a missing source
or runtime-library symbol.

The native-project import matcher treated `compiler.loader.smf_mmap_native` as
a non-contiguous subsequence. It matched both the exact owner module and the
nested wrapper module `compiler.loader.loader.smf_mmap_native`, which defines
the same `native_*` names. The resulting ambiguous import omitted the alias
from the per-module use map, leaving the raw alias in the object.

Focused reproduction: `test/fixtures/macos_alias_link/` contains an owner,
a nested same-named wrapper, and an entry calling both. With the frozen Stage 2
compiler (SHA-256 `7f6283bc9a2b7e9d7ef7078b5c3bc7fbba49a54d3d6b61f83bb3cd0540a55821`),
`native-build --entry-closure --source test/fixtures/macos_alias_link
--entry test/fixtures/macos_alias_link/main.spl` failed with undefined
`owner_probe_value`. Its retained objects defined both
`_loader__owner__native_probe_value` and
`_loader__loader__owner__native_probe_value`, while the wrapper object
referenced `_owner_probe_value`.

The fix gives exact full module ownership precedence, then a qualified suffix,
then the existing subsequence fallback for tier-inserted stdlib paths. It
scans only the candidates for one imported name; no full-tree search or
per-call runtime work is added. The native-project tests pin exact ownership,
the fallback, and absence of a bare alias in an emitted archive.
