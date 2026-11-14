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
provider digest declares the managed compiler lineage containing the builtin adapter,
not a source advice function. It is not generic proof of the executing image: the
validated managed launch chain must bind that digest to the launched executable;
ordinary/LSP entry paths require their own typed image identity. Fresh process-local
matching does not authorize serialized output reuse. Directory
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
category projections now reuse the exact semantic owner folds, with separate
category domains; the whole frozen interface hash is not relabeled as a category. Missing sections require coverage
proof before claiming an empty category. This work and B3 inline facts, traversal
cutoff/publication and a complete acceptance run remain required.


## Partial category capture at full-source parsing

`module_surface_trait_root_v2` covers trait declarations and default method bodies;
`module_surface_extension_root_v2` covers impl signatures and enum extensions,
preserving the existing whole-surface order and encoding. Ordinary impl method
bodies remain outside this interface projection. The legacy whole-surface encoding
was independently reconstructed unchanged during Astra review. Eight parser-based
regression scenarios are authored but not executed.

`project_directory_categories_v2` now calls these owners inside the actual streaming
surface parse scope. It requires successful full-source parsing (not skeleton or
placeholder text), an existing full-inventory cfg receipt validated against the
actual source SHA and target, and a valid composition-root environment policy
digest. The compact receipt binds source identity, target, preprocessing and cfg
decisions, environment policy, and both category roots. Only that receipt is
promoted; no parser AST survives through this route. The context dictionary is
updated after successful surface insertion and reset at source-lineage loading.
Missing coverage omits a receipt and does not grant empty-category authority.

These are compile-local partial receipts. A final directory producer must establish
exact member coverage and common variant, separately bind the executing provider,
and combine the remaining real category/initializer receipts before PackageInit
publication. No new cache cutoff or full-package admission is enabled here. The
three structural transport scenarios and production full-parse hook are currently
unrun; this checkpoint does not upgrade prior codec/row probe evidence.


## Executing image versus declared producer

Snapshots now carry `executing_image_digest` and `declared_producer_digest`
separately. The latter remains checked managed inventory lineage. The former
comes from the lazy typed `CompileContext.kernel_image_digest_provider`, which
observes the Linux kernel executable image, caches success/unavailability once
per process, and has no environment/argv fallback. Capture requests it only after
aspect claims and basic lineage validation. Unsupported observation yields no
snapshot and full traversal. The builtin plugin code key uses the executing-image
digest plus its stable entry/schema; configured producer roles are not assumed
equal to the running worker. Missing executing-image transport is rejected.
These are process-local inputs, not serialized admission tokens. The owner has a separate admitted-P2-built Linux/AArch64 native probe recorded in
`doc/01_research/local/kernel_image_digest_v1_native_probe_2026-11-14.md`. The new
capture fallback spec and whole directory route remain unrun.


## Initializer plan ownership

The actual `lower_runtime_module_initializers_named` owner now captures the
ordered globals after its declaration-order selection and function-slot append.
It records compact symbol/name steps and the emitted initializer symbol on
`MirModule.initializer_plan_v1` only after successful wrapper generation. It clears
prior state on entry. `Some` with an empty plan means the owner actually ran and
found no runtime work; `nil` means unavailable. The borrowed primary-globals route
preserves the first emission's plan alongside the reused initializer MIR.

AOP, debug tracing, XRay and the inspected optimizer reconstruction paths preserve
this historical plan. Preservation does not establish the final transformed body.
The bootstrap flattening store transports it through its existing ownership and
publication protocol. Parser/HIR/MIR plan scenarios and bootstrap ownership
scenarios are authored but unrun. No initializer wire roundtrip is claimed.

Finalization still must join this plan to the actual post-transform MIR, checked
emitted objects and the backend's actual startup sequence. That sequence currently
sorts/deduplicates defined module-init symbols; it is not a newly inferred dependency
order. The existing native link receipt owner already binds ordered object digests,
link options and output content after successful linking. Extending that explicit
versioned owner with the actual startup receipt, then joining module plan coverage,
is required before complete PackageInit publication or initializer reuse.

### Initializer object/startup observation integration (implementation, unqualified)

The actual accepted native capsule path now captures initializer-body observations
before MIR eviction. It reuses the capsule owner's verified object digest/size,
requires a matching full-parse category source/target/policy receipt, and observes
the executing image lazily. Each attempted module capture clears its previous
receipt; a new source lineage clears the table. Missing MIR or historical plan,
stale source, unsupported image observation, and unavailable scratch ownership
produce no receipt. Serializer scratch uses a transient scope; only the compact
receipt survives. This is a compile-local partial object observation, not complete
PackageInit authorization or a proof of preserved historical effect ordering.

Typed backend wrappers preserve existing callers and carry checked startup names
in their actual emitted order only when strict discovery and source/object byte
observations succeed. The existing atomic link-receipt writer can persist the
version-2 format with actual ordered input object digests and final output digest.
Retained receipts remain explicitly unknown for fresh startup authority; callers
requiring fresh observation bypass reuse. Old and unqualified backend routes
remain unknown. Default XRay thread-context policy remains false; enabled policy
is forwarded only through the admitted source-built runtime route.

The new initializer finalizer, typed backend scenarios, codec specifications and
actual object capture have not been executed. Existing codec/source-row checks do
not qualify these additions. Full directory membership/category aggregation,
object coverage and the final startup/output join remain required before publishing
a complete PackageInit record.

### Current-build initializer aggregate (source implementation, unrun)

All four hosted final-link call sites now enter an optional observation wrapper.
It requires a unique current module/category receipt for each selected object
path, retains selected object order, rechecks object SHA before and after the
fresh typed link, and requires the observed startup symbols to equal the complete
expected set. The backend's actual startup order is retained unchanged. The
aggregate binds final output SHA, current executing image, target and environment
policy. Every attempt clears an earlier aggregate. Unsupported external, warm,
objectless or incomplete coverage follows ordinary linking without an aggregate.
No persisted receipt creates fresh authority.

This join and two new pure symbol-set specifications remain unrun. It is a
current-build initializer observation only; it does not publish PackageInit or
replace the still-required macro/aspect/generic category and full-directory
aggregation. The kernel-image memo qualification blocker remains applicable.

### Source-load epoch for category drafts

`DirectorySourceEpochV2` correlates phase2 draft capture with later HIR category
finalization. The actual source-load owner advances its checked generation and
binds the driver identity after clearing prior projection/aggregate state, before
any new source work. Exhaustion leaves the epoch unavailable and never wraps.
This is not source/provider authorization and is not serialized as semantic
identity. Existing AOP-lowering and diagnostic traversal generations remain
separate. Two focused epoch specs are authored, unrun. Full native qualification
is planned in `doc/03_plan/compiler/aspect_dynload/directory_tldr_native_qualification_2026-11-14.md`.
