# Directory TLDR roots: schema 2 producer and snapshot comparison

Date: 2026-11-14. Status: implementation slice; full REQ-DTA-A1/B3/H1 remains open.

The existing `PackageInitTldV1` owns the format. Four optional fields extend it:
`file_tldr_root_digest`, `join_point_facts_digest`, `compiler_provider_id`, and
`active_guard_root_digest`. All absent preserves byte-for-byte PIT1 schema 1;
all present requires envelope and payload schema 2. Partial extensions fail.
Old readers reject schema 2. Stage-2 readability requires an executed reader
roundtrip; this design does not infer it from accepted source syntax.

The member root hashes exact file-TLDR bytes supplied by `SourceReader.read_tldr`,
not source hashes. Its domain-separated leaves bind member ID and digest; binary
nodes bind ordered children; the final root binds leaf count. Members must be
strictly ordered and unique. Missing or stale reader results fail production.
The driver adapter does not regenerate missing metadata or publish a cache.

Facts remain owned by `aspect_match_shard_v1`. Production checks complete scope,
exact membership, bounded canonical point/child identities, and a recomputed facts
key. Tagged SHA256 facts and guard digests retain their existing representation.
The directory identity binds package, parent, membership, compiler/provider and
guard; the canonical output digest additionally binds the content roots. A file
TLDR edit therefore invalidates output without renaming its directory owner.

`package_init_directory_compare_v2` compares stored bytes against **trusted fresh
producer inputs**. `DirectoryTldrViewV2` is a publicly constructible structural
snapshot, not an unforgeable admission capability. The caller establishes source
snapshot freshness, evaluated guard completeness, negative-witness correctness and
provider identity. Neither expected facts nor expected roots may be reconstructed
from the stored cache record itself. Physical checksums prove structural binding,
not this semantic authority. Legacy data can decode but cannot satisfy schema-2
snapshot comparison.

The package format never owns plugin instances, prior match shards or prior
application maps. The plugin planner may consume the same facts through its own
in-memory view; the package view does not introduce a second plugin contract.

## Remaining selected work

- Connect this reader adapter to the compiler's authoritative directory snapshot
  and cache admission/publication path, including guard and negative witnesses.
- Implement B3 inline join-point facts with the existing physical section owner.
- Integrate C1 traversal cutoff, old/new membership, H3 single-flight and atomic
  publication, plugin updates and pointer traversal. This slice does not claim
  those features or complete A1 acceptance.
- Execute the new specs on an admitted pure-Simple runtime and broad compiler/lib
  and MCP/LSP gates before production qualification.

Unit fixtures cover unchanged legacy bytes, explicit schema roundtrips, truncation,
corruption, physical binding, stale content, identity changes and deterministic
Merkle roots. Test presence is not evidence of execution.

## Verification checkpoint

The exact codec and helper extraction compiles with the retained pure P2, but
native execution fails in the text-byte provider before legacy encoding. An
unchanged release-codec control reproduces the same failure. See
[producer-bound report](../../bug_report/p2_text_bytes_codec_probe_2026_11_14.md).
Schema-2 runtime roundtrip, Merkle/reader unit specs and broad runtime checks remain
unqualified. Astra source review found no P0/P1 in the scoped producer/comparator;
that review does not replace runtime evidence or complete the selected feature.
