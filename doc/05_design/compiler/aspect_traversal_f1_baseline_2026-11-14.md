# F1 traversal: authoritative baselines and real caller

Status: architecture reviewed; cold-visit source implementation in progress. No F1 runtime qualification yet.
This continues the selected F1 requirement. It does not reopen the six completed
normalizer/pool/driver/MIR qualification cycles.

## Existing owners and missing authority

`TraversalPlugin.visit(DirTldrViewV1, PointcutSelectorV1)` must return the existing
`WeavePlanDeltaV1`. The existing pointcut matcher and static HIR/MIR weavers remain
owners; neither a second matcher nor runtime-around is introduced. Closed MIR
placement landed in PR #9178. HIR forwarder weaving is a separate phase.

The integrated directory snapshot producer supplies frozen membership, file-TLDR,
guard/fact and checked declared-producer lineage. Executing-image identity is a separate new owner integration, not inferred from configured lineage. Its actual driver caller
uses the builtin descriptor adapter only after that gate. Current forward facts
still carry an empty `base_body_digest`; they cannot authorize unweave or reuse.
The unused `AspectWeaveBaseBodiesV1` helper does not constitute a production
immutable baseline.

Real body owners are `hir_module_encode_canonical` and the bounded canonical
module decoder. The generated function/block codecs are implementation leaves;
there is no public standalone canonical function snapshot API today.
`hir_abi_function_digest_v1` supplies actual declaration/signature/effect identity,
explicitly excluding implementation. Whole-source SHA is not a function-body
identity.

## Proposed implementation boundaries

- `00.common/cache_contract/aspect_traversal_v1.spl`: pure `DirTldrViewV1`,
  checked construction, `TraversalPlugin` and a deterministic builtin adapter
  delegating to the existing delta function. Views contain immutable current and
  prior same-scope selection/application facts, not compiler mutation authority.
- `80.driver/cache/aop_traversal_inputs_v1.spl`: bounded cold canonical module
  digest capture and real advice
  identity resolution and application-key construction. Immutable retained
  baseline/output storage remains a subsequent implementation. No filesystem
  or native code loading is introduced.
- Existing `aop_weave_with_match_cache_v1`: actual consumer, preserving the
  snapshot gate and live forwarder revalidation. The directory owner and F1
  owner coordinate this one integration point.
- Existing `aspect_weave.spl`: actual rewrite on misses. No new weave logic.
- `compiler_schema/visitor_gen.spl` remains owner of generated reverse child
  frames. Pointer-child generation is distinct from node-view accessors and
  from this directory-level F1 adapter; a separate generator change requires its
  own concrete generated consumer.

## Baseline and publication rules

Start conservatively with immutable canonical **module** bytes, checked provider
identity and qualified function identities. A module digest is an explicit
coarse body root; do not label it a standalone function-only digest. This may
invalidate extra work on unrelated body edits but cannot reuse a stale body.
Capture before weaving, once per admitted source epoch. Bound count and total
retained bytes; unavailable codecs, ambiguous advice owners, missing signatures,
unsupported forms, incomplete snapshots and resource limits take the existing
full-visit path without publishing a reusable entry.

Only actual contract path plus advice function resolution can provide advice
identity. No name-only or synthetic compiler-version digest substitutes for
content. Canonical bytes must be compared on cache hits where a digest collision
could otherwise substitute another body. Provider changes invalidate retained
outputs. Reconstructed HIR comes from the bounded existing decoder; decoding
failure is a miss, never an empty successful module.

Preserve sequential claim semantics: the existing first rewrite may make a
function cease to be a pure forwarder, causing later claims to skip it. An
aggregate ordered-claim output cache must preserve that behavior; alternatively
stage keys must include predecessor output identity. Naively applying every
advice from the same baseline changes the language and is prohibited.

The pure per-claim delta can guide invalidation, while a module with any changed
application is rebuilt through the existing complete ordered claim loop from a
verified immutable baseline. A wholly reused module requires exact base,
provider, ordered claim/signature/effects/body identity and scope agreement.
Removed claims must be considered before the current empty-claims early return.
Restoration uses verified current source baseline, not an old borrowed HIR block.
Repeated visits to the same already-woven module require an exact prior-output
binding **and the same real source/lowering epoch** for restoration. If authority
disappears, never run the legacy loop over that woven input or take the empty-
claims early return. Restore only under the exact binding; otherwise return a
checked error requiring fresh lowering/rebuild. Do not reclassify arbitrary
mutated or new-epoch HIR as a fresh source baseline. The actual
`CompileContext.aop_source_epoch_v2` owner must supply this lifetime fact; a
synthetic counter in the plugin is not a substitute.

A public DTO is not an admission token. The checked view constructor validates
consistency; the actual frozen source producer supplies authority. Full facts
must be complete for the relevant source directory, not merely the subset of
modules currently materialized. No partial snapshot may authorize traversal
cutoff, body reuse or unweaving.

## Separate F1 acceptance plan

The new package has distinct behavior criteria and does not reset earlier
verification attempts:

1. Actual producer binds nonempty immutable canonical body and advice identities;
   mutation of a retained HIR object cannot mutate stored baseline bytes.
2. Cold visit emits deterministic weave work; unchanged input reuses output and
   existing selector/match results without re-running rewrite.
3. Target/advice-body/selector changes produce the appropriate existing delta;
   removed advice restores the verified baseline, including the zero-claim case.
4. Multiple claims preserve legacy ordering/live-forwarder decisions, and repeated
   visits do not duplicate advice.
5. Provider/scope mismatch, incomplete membership, unknown advice identity, codec
   refusal/corruption and memory limits force full traversal only for verified
   fresh lowering. Previously woven inputs require exact-output/same-epoch
   restoration, or a checked refusal requiring rebuild; never leave stale advice.
6. Actual generated/native HIR consumers match an uncached baseline's function
   result and advice sequence. Pure delta tests alone cannot qualify this gate.

Test fixtures must use actual codecs/types/weavers, retain source/producer/cache
provenance and report unsupported cases. No performance, H5 plugin admission,
full pointer-generation, whole-feature or Phase 3 completion is implied.

## Concrete interfaces under review

The selected trait spelling is preserved:
`TraversalPlugin.visit(dir: DirTldrViewV1, sel: PointcutSelectorV1) -> WeavePlanDeltaV1`.
A separate checked factory returns `Result<DirTldrViewV1, text>`; refusal is not
an empty successful delta. The view binds scope/provider, current facts/shard/
apply keys and optional prior facts/shard/apply keys. Prior/current selector and
scope associations are checked explicitly. A cold visit is an explicit absence
of prior state, not a fabricated old snapshot.

Proposed driver storage names are `TraversalModuleSnapshotV1` and
`TraversalOutputCacheV1`: module identity, source epoch/binding, provider,
immutable canonical baseline/output bytes and digests, ordered claim identity,
per-claim prior states and rewrite count. Capacity and retained-byte limits are
checked before publication; decode finishes before replacing any live module.
A real context once-per-epoch weave marker is needed when uncached fallback
occurs, so a later visit cannot mistake previously woven data for fresh input.

## First implementation slice: cold visit only

The actual context owns `aop_traversal_started_epoch_v1` and
`aop_traversal_completed_epoch_v1`, reset at the three actual lowering entry
points. The validation gate marks started before any weave, including the
zero-claim path, and rejects a second attempt until fresh lowering. A new epoch
can legitimately have bytes equal to an old woven output; byte equality does
not replace this freshness authority. No output/baseline retention is claimed.

The cold input owner encodes each module once for the complete ordered claim
batch, retaining only coarse digests. The current cold implementation uses
bounded ordinary-format bytes; canonical persistence remains separately gated. Actual advice function resolution uses
registry owner path and function name with ambiguity refusal. Signature and
effects come from the actual HIR ABI encoder; effects are encoded separately.
The concrete forwarder weaver prepends static calls, so its facet is before /
static, independent of physical MIR advice forms. Existing sequential live
forwarder guards still determine actual rewritten bodies.

`executing_image_digest` names the observed current compiler image for builtin
code identity. `declared_producer_digest` names configured/inventory lineage.
They are distinct roles and are not blindly equated. Neither a digest-shaped
string nor the public view DTO establishes authority. Snapshot capture must
obtain the former from the reviewed KernelImageDigest owner before authorizing
this path. Old records missing that evidence fall back on fresh input.

This first slice does not satisfy acceptance 2 warm-output reuse, acceptance 3
restoration/removal, generated pointer-traversal production, H5 plugin loading,
or the full F1 requirement. Native fixtures must report those gaps explicitly.

The checked view currently recomputes the existing matcher to validate exact
selection/apply coverage even after a shard-cache hit. This is a deliberate
cold correctness check, not qualified match-scan avoidance or a warm speedup.
A trusted prepared-view route and measured evidence are still needed for that
optimization. The first capture limits are 1,024 modules, 8 MiB total snapshot
text and 65,536 function roots; the canonical codec also enforces its own
allocation limits. The per-instance implementation map is capped at 256, like
the existing descriptor pool. Canonical body bytes are transient, not retained
restoration state; only the original digest values survive the ordered rewrite.

## Cold boundary qualification, 2026-11-14

The new F1 package has used two bounded attempts: the first was refused before
compilation because the private fixture had no Git HEAD; the source was pinned
and the second compiled in 15.1 seconds under 60 seconds / 2 GiB address space.
The admitted pure-Simple P2 SHA-256 was
`855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`.
The resulting native executable passed 13 assertions of the exact new checked
view/trait and existing matcher/delta: cold weave, unchanged reuse, changed-apply
reweave, selector removal, missing/extra apply entries, wrong scope, mismatched
selector, changed executing image, incomplete facts, duplicate IDs, invalid
image identity, and one stateless implementation used across two directories.

Evidence is retained in `/tmp/aspect-traversal-contract-probe-20261114`: exact
projection recipe and source hashes, pinned fixture, compile/run logs and
`provenance.sdn` with source/binary hashes. Synthetic image/apply inputs exercise
the pure checked boundary only. This does not execute canonical HIR capture,
the actual driver loop, full module imports, source snapshots, restoration,
plugin loading, or the authored SSpec files. The native build warning that
automatic dynload aspect-pack packaging is unavailable remains applicable.

`aspect_traversal_inputs_v1_spec.spl` separately specifies real frontend/lowering,
canonical codec, ABI/effect and existing-weaver behavior. It is authored but
**unrun**, so real producer/body-capture runtime qualification remains open.
The previous descriptor/MIR work package's six attempts remain exhausted;
these distinct F1 criteria do not reopen or repeat those passing checks.

### Canonical codec blocker discovered before producer execution

The current `hir_canonical_codec_generated_available_v1()` deliberately returns
false until its own admitted regeneration/golden-byte gate is completed. Thus
the first cold capture implementation returns unavailable on this base and the
actual driver safely executes its full-visit fallback. The 13 boundary checks
do not establish that this production cold path activates. The canonical gate
is not bypassed or marked passed. A bounded ordinary-codec snapshot alternative
is under architecture review; it must retain a distinct noncanonical contract
and cannot claim canonical persistence or baseline restoration.

### Reviewed cold-only ordinary snapshot update

The follow-up `hir_module_encode_snapshot_bounded_v1` reuses the owning ordinary
encoder with output/allocation/work/depth limits enforced during emission and
header assembly. Capture passes the remaining batch output allowance before
encoding each module. Overflow, unsupported bodies and representation metadata
return an error with no usable partial snapshot. The canonical availability
function remains unchanged and disabled.

The application key now uses the distinct `simple/aop-ordinary-module/v1`
domain. Exact ordinary bytes cover real bodies and may overinvalidate on
incidental ordering differences; they are not called canonical portable bytes.
No persisted warm-output/restoration key is authorized by this cold API. This
source-level change removes the always-unavailable API choice from cold capture,
but its real producer runtime behavior is still unqualified. Astra accepted the
source contract; the independent canonical lane owns actual codec fixture
preparation. The 13 pure-boundary results are unchanged and were not rerun.
