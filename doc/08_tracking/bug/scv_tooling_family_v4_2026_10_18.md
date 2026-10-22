# Finite tooling source inventory lacks cursor authority

Date: 2026-10-18
Bug: BUG-SCV-TOOLING-FAMILY-V4-20261018
Database reconciliation: pending; no qualified full CLI bug-database tool available.
Status: source-confirmed; source repair and regressions UNRUN natively.

At release_phase3 2bcc8144b1bf4b16af66d6c0a5c9bd76e1c3ac8f, bootstrap-from-scratch.sh's genuine full-CLI recipe selects examples/10_tooling. source_authority.spl compiler_source_authority_inventory_roots_v1 admits only src/test, returning[] for that canonical selector; native_build_main reports SCV-E-ADMISSION source-inventory-scope-unsupported before parsing. Its blob0d6ecb1d87d9dea76ef43663014f57c8bd4fa4ba also exactly matches the ee3-based producer. This is a source proof, not an executed reproduction on the new2FA6 producer.

An authority-only whitelist change is insufficient: event cursor, untracked digest split, membership encode/decode/merge, deletions and pointer publication must attest the same finite family. Otherwise a warm cursor can miss tooling changes or deletions while appearing valid.

## Repair

Five production owners add exactly the closed family examples/10_tooling beside src/test. Canonical selector normalization and pre-normalization traversal rejection remain in their existing owner; exact family or slash-descendant boundaries reject sibling prefixes, broad examples, outside paths and invalid components. Snapshot selectors remain exact and physical ownership checks remain unchanged.

A separate untracked_examples_tooling_digest travels through event batches, cursor records, membership reconciliation, trace and atomic CURRENT publication. Cursor v4 has ten ordered rows with valid digest shape; wrong row count/version/name rejects. Existing v1/v2/v3 calls retain their prior contracts. A legacy cursor may still serve src/test, but cannot attest tooling: selecting that family without its digest fails closed and requests the existing supported cold-init owner. That owner scans the three finite families and publishes a real v4 binding. No tooling facts are packed into src_digest; no arbitrary examples/** source is admitted.

The single global Git HEAD now captures committed changes across all three closed families when advancing, even if today's snapshot selects only one family. Untracked selection and authenticated membership merge/deletion preserve unselected family facts. The pointer reader bound increases from768 to1024 bytes to cover the longer valid v4 record; oversized records still reject before admission.

## Scope and provenance

The five-owner implementation derives from earlier reviewed source-only9122938c2a98f4a4eb4b9af2f45c05e300ee46ca. All four existing owner blobs were byte-identical between that old baseline29d68488914 and current2bcc, so the finite patch applies without unrelated changes. The fifth inventory_families owner is new. This is implementation provenance, NOT borrowed native qualification: that older native fixture stopped at an array-comparison-induced failure and did not qualify six controls.

No old failed fixture, array equality oracle, gzip repair or separate optional-owner-join workaround is included here. The existing initializer expression remains unchanged. Historical optional-owner join failures and remaining generic AST If ownership hazards are separate; this source repair does not establish that a new producer can already compile all product closures.

The isolated source worktree physically materializes the entire tracked examples/10_tooling subtree from its frozen Git source for future cold-sweep work. Other source hydration remains intentionally sparse and is not a build-ready full-source claim. No source snapshot or SCV pointer was fabricated and no compiler/cache identity stamp was rewritten.

## Real regressions and limits

New tooling_family_v4_spec.spl and helper fixture use scalar len/index/content oracles, not array/record identity. Cases cover actual canonical selection; sibling/traversal/foreign/control rejection; membership roundtrip, duplicate/outside rejection, selected replacement/unselected preservation; exact v3/v4 cursor versions and malformed digest rows; real Git+filesystem eight-scope acquisition, cross-family committed changes, immutable snapshot preservation, mixed/wrong generation rejection, tooling untracked add/delete and digest invalidation; genuine publisher-produced v3 authority refusal followed by real cold migration; maximal legal v4 pointer reading within1024 and oversized rejection. Reader-bound adversarial records never enter source admission.

All new tests are UNRUN. Native/full compiler/lib/MCP/LSP gates remain UNRUN. This change is source-only and cannot satisfy the full-CLI/test-runner or Phase4 requirements until a genuine rebuilt producer, strict linking, and actual qualification controls pass. No compiler/native build or executable execution occurred in this lane. Mandatory broader gaps remain visible in the draft PR.
