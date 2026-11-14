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

The first retained pure-P2/default-runtime probe failed in the text-byte provider
before legacy encoding; an unchanged release-codec control reproduced it. See
[producer-bound report](../../bug_report/p2_text_bytes_codec_probe_2026_11_14.md).

Cycle 5 used the newer admitted pure-P2 SHA256
`855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`
with the supported explicit `--runtime-bundle core-c`. The unchanged exact feature
codec/helper extraction compiled and passed 11 native checks: legacy encode,
decode and roundtrip; schema-2 encode, decode and roundtrip; legacy envelope reader
rejection of schema 2; provider identity preservation; partial extension rejection;
schema disagreement rejection; and trailing-byte rejection. The production codec
block SHA256 is `1f634ccfc7d22122bf52f239c4c245802b7fd529b59dfd50cd7376400f3c6be1`.
The extracted source SHA256 remains
`d3eb2fcee40238e11ce8547ebbbb906524db0bf6c2a5b44ae509a5e2faab9396`.

Evidence: `/tmp/dir-tldr-codec-probe-20261114/compile5.log` and `run5.log`,
with the command from the bug report plus `--runtime-bundle core-c`, private
`cache-core-c`, and output `codec-probe-core-c`. This qualifies the codec roundtrip
with that explicit runtime profile, not the default mixed-runtime bundle.

Merkle/reader unit specs, physical binding execution and broad runtime checks
remain unqualified. Astra source review found no P0/P1 in the scoped
producer/comparator; that review does not replace those runtime checks or complete
the selected A1/B3/H1 feature. The subsequent source-bound consumer integration is described below; full PackageInit cache admission is still open.

## Source-bound production consumer checkpoint

The HIR pipeline now captures an immutable matching snapshot once per lowering
context, including an empty failure result. Its supported provenance route is the
checked native-group source loader. That route binds compiler producer, pinned
inventory, SCV revision and tree; an ordinary working-tree/LSP compile without
that authority falls back to the existing full live weave. No environment string
alone grants a directory hit.

`directory_tldr_snapshot_capture_v2` reopens the pinned source inventory and SCV
snapshot through their existing readers, checks binding and generation, and
requires the HIR/phase-1 source rows to cover every immediate inventory member.
Aliases, duplicates, subsets, source SHA/length disagreement and missing/stale
companions prevent capture. The companion's embedded source digest must match the
phase-1 receipt. The source-row comparator is also called by the real producer.
Capture retains at most 32 MiB of frozen source text; larger inputs conservatively
miss. With no aspect claims it performs no snapshot reads.

The attribute registry now distinguishes an absent/restored row from a known-empty
row in the active lowering epoch. Epochs never wrap; resetting proof rows preserves
the legacy attribute getter. The capturer requires fresh rows for selected forward
functions, so restored HIR without attribute rehydration cannot acquire proof.
Guards are evaluated from the same frozen source map. Target/profile disagreement
or unevaluable guards prevents capture.

Three actual HIR validation call sites pass these snapshots to the existing weave
owner. The consumer uses captured facts directly, checks full held-module coverage,
and calls the provider-bound builtin plugin adapter. Missing coverage, malformed
transport or plugin errors trigger the existing whole-module traversal, preserving
the live forward-shape check. This does not unweave or suppress a needed visit.
The direct semantic-owner match API remains available without pretending it is a
persisted directory admission route.

This integrates the reviewed plugin-model dependency from PR #9172. The compiler
provider names the builtin adapter code, not a source advice function. Directory
configuration is scope data, never retained as instance configuration.

The file-TLDR root hashes actual companion bytes. Source freshness and current
companion framing do not establish which compiler produced that metadata; matching
continues to use fresh HIR facts. Full PackageInit semantic admission still needs
explicit companion producer/version evidence before trusting semantic contents.

Verification: an exact source-row/attribute-epoch extraction compiled with admitted
P2 SHA855f48 and explicit `core-c`, then passed 18 native assertions in
`/tmp/dir-tldr-snapshot-probe-20261114/{compile.log,run.log}`. It covers complete and
subset membership, aliases/duplicates/order, stale source digests/lengths, known
empty/absent attributes and retired epochs. Six authored unit scenarios and three
real-parser/HIR consumer scenarios supplement this probe; those specs and the full
SCV/FileReader/HIR integrated route have not yet executed. The codec's earlier
11-check pass is retained, not rerun.

## Remaining full PackageInit projection

The full end state still derives category roots from actual owners, not empty
placeholders. Generic-template roots can consume
`build_generic_template_section_v1` reached by the real module-artifact producer;
macro roots can consume source-bound `macro_input_root_v1`/`macro_effect_surface_v1`
with validated tagged-digest conversion. Compiled initializer digests exist in
`cold_hir_package_outputs_from_driver_v1`, but directory initializer ordering still
needs its explicit owner. Aspect catalog/advice-interface roots are currently
broader than a directory and require scoped aggregation. Trait and extension
category projections still need implementation; the whole frozen interface hash
is not silently relabeled as either category. Missing sections require coverage
proof before claiming an empty category. This work and B3 inline facts, traversal
cutoff/publication and a complete acceptance run remain required.
