# Explicit stable-symbol redirects v1

Authored manual for `test/01_unit/compiler/semantics/symbol_redirects_v1_spec.spl`.
Execution, docgen, branch coverage, native ownership and performance: **UNRUN**.
This file is authored from the spec; it is not generated execution evidence.

Selected traceability: REQ-MC-008, B1 table/index foundation, canonical06-1
DOC-STABLE-IDENTITY. The frozen identity schema1 stays unchanged. Callers supply
explicit old/new resolved declaration components; fixtures do not establish an
actual semantic editor rename producer.

| Scenario step | Observable checks in the real library/index |
| --- | --- |
| Resolve an explicit name-only rename through the actual index | Old full ID resolves to independently derived live new ID; current ID resolves itself; unknown stays empty. Current count/module/short lookups retain their meanings; aliases are full-ID-only. |
| Preserve frozen identity and legacy index behavior | Schema1 and fixed golden ID remain stable; empty redirects, duplicate live declarations, empty index and legacy forced short collisions retain behavior. |
| Reject identity changes instead of guessing a rename | Package/module/kind/owner/type/arity/return changes refuse construction. Existing normalization accepts declaration/parameter-name, default and whitespace differences without adding signature policy. |
| Refuse ambiguous and malformed redirect histories | Conflicts in both orders, same-ID/self edges, unsupported version, two/three-node cycles, unindexed terminal and live-source ambiguity refuse construction. Identical rows remain idempotent. |
| Resolve chains once with deterministic terminal ownership | A→B→C resolves to C in both input orders; distinct histories may converge. Direct-edge metadata and unique counts stay exact. |
| Bound history work and preserve lookup ownership | A 128-edge history, shared tail, repeated reads and long cycle use real index snapshots with exact results/counts. This functional loop makes no timing/RSS claim. |

Construction validates every row using unchanged `stable_symbol_id` and
`normalize_signature`; no raw-signature equality or similarity search is used.
The current index's existing collision gate runs first. A failed table never
escapes inside a partially usable returned index. Unique direct edges are
retained, then an iterative bounded path-compression pass owns each historical
source's terminal. Lookups use exact map reads through `me` receivers. Empty
rows avoid the graph pass and live-ID collection.

Expected construction/storage bounds are O(N+R+component-text-size) work and
O(N+R) retained/scratch storage, excluding cryptographic/text processing. These
are source-level design bounds, not measured native results. Qualified-engine
execution of this spec, existing symbol-ID spec, core checks and MCP smoke
remain required before runtime/production readiness can be claimed.

Remaining feature work includes actual declaration/rename-event authority, B5
atomic source/Markdown transactions, B2 historical-link consumers, B3 lint/fix,
B4 rendering/LSP, selected persistence/revision admission, and runtime/ABI/
allocation/latency/RSS qualification. This stage does not close REQ-MC-008.
