# Link Manager Contract v1 (LINK lane — resolve contract freeze)

**Date:** 2026-07-31 · **Status:** Frozen (v1)
**Parent:** architecture Part VII §18–§19, §29 Wave 7;
plan `doc/03_plan/platform/structural_compute/link_manager_plan.md`.
**Peer conventions:** `identity_tagmap_contract_v1.md` §2 is normative here —
this document freezes only what LINK adds.

## 1. Module placement

| Artifact | Path |
|---|---|
| Frozen types + `ResolveProfile` trait | `src/lib/common/structural/resolve/resolve_types.spl` |
| CPU reference codec (the oracle) | `src/lib/common/structural/resolve/resolve_codec.spl` |
| Facade (explicit exports only) | `src/lib/common/structural/resolve/__init__.spl` |
| Contract spec | `test/01_unit/common/structural/resolve_contract_spec.spl` |
| Golden vectors | `test/fixtures/structural/resolve_golden_v1.{spl,sdn}` |

The plan names `test/01_unit/lib/structural/resolve/` as the spec path; the
in-tree convention set by the ID-TAG freeze is
`test/01_unit/common/structural/`, which this lane follows (raised in §7).
Profile implementations (SmfLinkProfile in
`src/compiler/70.backend/linker/gpu_smf/`, StyleLinker, ClangOffloadLink) are
implementation waves, not part of this freeze.

## 2. Reused frozen contracts (consumed, not redefined)

- **Identity:** `EntityRef`, `SnapshotId`, `Hash128` from
  `structural/identity` — LINK mints no parallel identity model.
- **Wire:** all byte-level conventions from `structural/wire.spl`
  (LE, u8 discriminants, u32 counts, 8-byte envelope, total decoders).
- **Placement/receipts:** `StageReceipt`, `PlacementBackend`, lease flow from
  `compute/placement_contracts` (gpu_mmu freeze `75e6b1e8435b`) — resident-tier
  arenas for symbols/relocations/output chunks come through that trait; LINK
  contributes only the `SMF_LINK_STAGE_L*` stage ids receipts are keyed by.
- **Tags:** `link.*` tag *names* are frozen here as constants; the tag value
  machinery is the ID-TAG TagMap contract.

## 3. Frozen wire layout (RESOLVE group, schema v1)

| Record | Bytes | Magic | Layout |
|---|---|---|---|
| ResolveKey | 20 | — (embedded) | name_hash Hash128 \| space u32 |
| DefinitionRecord | 44 | `SDFN` | key ResolveKey \| owner EntityRef \| attributes u64 \| order u64 |
| ReferenceRecord | 44 | `SRFR` | key ResolveKey \| owner EntityRef \| attributes u64 \| order u64 |
| ResolutionRecord | 20 | `SRSL` | reference EntityRef \| definition EntityRef \| status u8 \| reason u8 \| reserved u16 (== 0) |

Enums (u8 on the wire, unknown = hard reject):

- `ResolveStatus`: 0 Unresolved · 1 Resolved · 2 Ambiguous · 3 WeakResolved.
  Zero is Unresolved **by design** so zero-initialized arena memory can never
  read as a successful resolution. `definition` may be dereferenced only for
  Resolved/WeakResolved (`resolution_definition_present`).
- `ResolveReason`: 0 Unspecified · 1 MissingDefinition · 2 DuplicateDefinition
  · 3 VisibilityDenied · 4 ArchiveUnextracted · 5 CycleDetected.
- `LinkMutationKind` (LINK's MutationIR projection, §12): 0
  ReplaceLinkDefinition · 1 AddRelocation · 2 ChangePlacementHint.
- `ResolveMode` (§19): 0 CpuReference · 1 HybridVectorGpu · 2 ResidentGpu.
  CpuReference is the byte-oracle for the other two.

## 4. Frozen interface surface

`ResolveProfile` (six steps, §18 — profiles share primitives, never
semantics):

```
trait ResolveProfile:
    fn collect(snapshot: SnapshotId) -> ResolveInputRef
    fn group_key(record: ReferenceRecord) -> ResolveKey
    fn resolve_group(group: ResolveGroupView) -> ResolveGroupResult
    fn derive_constraints(result: ResolveGroupResult) -> ConstraintBatch
    fn plan_placement(result: ResolveResultRef) -> DomainPlacementRef
    fn emit(result: ResolveResultRef) -> MutationPlanRef
```

Arena handles (`ResolveInputRef`, `ResolveResultRef`, `ConstraintBatch`,
`DomainPlacementRef`, `MutationPlanRef`, `ResolveGroupView`,
`ResolveGroupResult`) are in-memory `object_slot`/`generation` pairs in the
placement_contracts style — never wire records, never raw addresses.

SMF pipeline stage ids `SMF_LINK_STAGE_L0_DISCOVER` … `L12_MANIFEST_COMMIT`
(values 0–12) key `StageReceipt.stage` for the SmfLinkProfile. Frozen `link.*`
tag names: symbol.{binding,visibility,resolution}, section.{kind,alignment},
relocation.kind, reachable, icf.candidate, hot_order, output_range.

## 5. Versioning and compatibility

1. Any layout or discriminant change bumps `RESOLVE_SCHEMA_VERSION` and adds
   `resolve_golden_v2` — golden vectors are never edited in place.
2. Decoders reject unknown versions; there is no negotiation.
3. The CPU reference codec is the oracle and is never deleted; hybrid/resident
   encoders must produce byte-identical output (acceptance: parity by hash).

## 6. Deliberately not shipped in v1

- MutationOp/MutationPlan wire encoding (MUTATE-lane owned; LINK freezes only
  the kinds it emits).
- SmfLinkProfile record `attributes` bit assignments (frozen with the L1
  decode wave, as `smf_link` schema constants).
- Reachability frontier / constraint-propagation batch layouts (GPU-facing;
  frozen with the hybrid wave against real batch shapes).

## 7. Ambiguities raised back to the architecture owner

| # | Item | Architecture ref | Gap | Resolution taken |
|---|---|---|---|---|
| 1 | `ResolveKey` width | §18 "hash/intern" | no width given | Hash128 + u32 space discriminant (20 B) |
| 2 | `attributes`/`order` width | §18 record shapes | no width given | u64 each; profile-defined bitset semantics |
| 3 | `group_key` parameter | §18 `ResolveRecord` | `ResolveRecord` type not defined | takes `ReferenceRecord` (definitions carry the key already) |
| 4 | Spec dir | plan `test/01_unit/lib/structural/` | conflicts with ID-TAG precedent | followed `test/01_unit/common/structural/` |
| 5 | MutationIR ownership | §12 vs plan line 38 | no MUTATE-lane code exists yet | LINK ships kind enum only; wire format deferred to MUTATE |
| 6 | `reason` on a Resolved group with duplicates | §18 reduction | one `reason` field, not one per diagnostic | reduce_group sets status Resolved + reason DuplicateDefinition + diagnostic_count = extras (anomaly on success) |

## 8. Verification status

`resolve_contract_spec.spl`: 4 exact-byte examples against hand-derived
goldens, 3 asymmetric round-trips, 5 total-decoder rejection examples
(wrong magic, truncation, unknown discriminant, nonzero reserved, bounds).
Golden vectors were derived by hand from §3, not captured from the encoder.
