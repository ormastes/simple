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

Source `5174cc67df7` implements the five-file shared path. Initial executable
intent `31aa0b0eb56` preceded source changes. Final independent review binds
source and acceptance/manual through `d38027c870e`: no P0/P1. Eight scenarios
cover both architectures, independent image/TLV/binding data, binary-address
validation, optional None/Some(0) versions, selected unsupported exports, retained
unused metadata and actual client/umbrella command payload failures.

The old byte API validates/delegates, so equality alone is not an independent
oracle; the literal command, version, entry, relocation and binding assertions
remain necessary. Callsite review found no additional consumers of the migrated
slot/image helpers. The projection adds a linear metadata pass and a bounded
resident command scan, not a new byte read or hard-memory qualification.
Invalid provider metadata now rejects before malformed object contents; request
validation remains first. Current runtime recheck found both workspace release
binary directories absent; no seed/unadmitted substitute was used.
