# Environment-Optimized Dynamic Libraries — Design TLDR

One baseline-safe compiler core selects separately built parser provider
artifacts. The host environment authorizes execution; a target-codegen profile
describes generated code. They have separate identities. Eligibility checks
precede mapping, and selected provider generations remain pinned until calls,
callbacks, and device work retire.

The canonical target registry owns versioned triple-to-numeric mappings and
declared aliases, including the supported 64-bit SimpleOS userland triples.
Their three-part spellings retain explicit ABI IDs in registry rows. A live V2
use token authorizes a target projection. Profile
binding checks the architecture, ABI, object format, endian, and pointer width
against that projection. Its digest uses canonical content and selected feature
words, so aliases and owner-local serials do not split build/cache identity.
Registry replacement stops new use acquisition on old resolutions but retains
pinned projections until release.

The target build/cache owner must consume the live registry use and profile
binding before issuing a plan or cache key. That join is pending; a copied
binding digest alone grants no build authority. Parser scalar parity, emitted
and executed ISA evidence, and actual GPU completion remain separate promotion
gates. Production startup uses cached artifacts and does not compile an
optimized provider on demand.

Inspect `src/compiler/80.driver/canonical_target_registry_owner_v2.spl`,
`environment_variant_build_plan_owner_v1.spl`, and the full design for
the detailed contracts and open gates.
