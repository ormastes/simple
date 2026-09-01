<!-- codex-architecture -->
# TLDR: executable aspect mapping receipt bridge

Status: proposed, contract-first; no executable-aspect unmap has been added.

`_ModuleAspectOwnerV1` must gain a loader-private,
`ModuleAspectExecutableMappingOwnerV1` registry as the only mutable authority
for executable-aspect mappings. `common/structural/parallel_commit` owns a
pointer-free `ExecutableMappingReceiptV1` coordinate; `SegmentMapper` and
`SharedExecMapper` retain addresses and native release mechanics privately.

Final unpin needs a lower-layer prepare/commit lease: `aspect_pack` cannot call
up into the loader. The loader prepares the final lease, releases exact
registry rows through mapper-private delegates, then commits payload release.
Failure stays `ReleasePending` and is retried by the same owner.

Live receipt and byte limits plus a bounded terminal-result ring prevent
registry growth. Hot lookup is O(1); final release is indexed by exact facet
generation, never a global mapper scan or bulk `unmap_owner`.

Blocked prerequisites: current mappers return raw addresses only,
`apk_facet_unpin_v1` returns only `bool`, and `_ModuleAspectOwnerV1` has no
mapping registry or capacity/issuer state.
