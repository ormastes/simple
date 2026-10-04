# Typed Mach-O provider verification

STATUS: FAIL — full item4/Phase 4, SDK support and five-host execution remain open.

This necessary SDK dependency separates export/link metadata from binary VM
addresses. The actual hosted fixup/image path must consume typed providers while
the existing byte API retains binary validation before projection. It must not
manufacture dylib bytes, addresses, SDK versions or artifact authority.

Acceptance requires real binary providers on both architectures, independent
output/binding oracles in addition to byte-API equivalence, retained malformed
binary checks, typed metadata validation and preservation of absent versions.
Client/umbrella policies must remain visible and fail explicitly until their
actual access semantics are implemented. Selected unsupported export behavior
and direct library ordinals remain unchanged.

Both v4 and v5 readers, target-qualified dependency closure, full SDK binding,
managed internal admission and actual host execution remain required. Compilation,
SSpec/docgen, coverage, core/MCP/native and performance checks remain UNRUN without
an admitted deployed self-hosted runtime. Source and structural evidence are
recorded separately and cannot establish release qualification.
