# Placement contract v1 — frozen

PlacementRequest / PlacementPlan / lease rules, the seventh of the ten artifact
groups architecture §26 requires frozen before subsystem development. PLACE
lane (§27).

Architecture sections: §20.2 (placement request), §20.3 (placement plan), §20.4
(backend interface), §20.5 (lease-bound resident view), §20.9 (metadata
overhead), §4.1 (`EntityRef` validity), §3.4 (GPU virtual-memory research).

- Simple types + CPU reference codec: `src/lib/common/structural/placement/`
- Golden vectors: `test/fixtures/structural/placement_golden_v1.{spl,sdn}`
- Gate: `test/01_unit/common/structural/placement_contract_spec.spl`

## What this group does NOT redeclare

`ResidencyTier`, `AccessPattern`, `PersistencePolicy`, `ExecutionMode`,
`Hash256`, `DeviceMask`, `ObjectRef<T>`, `EntityRef`, `ResidentView<T>`, `PlacementRequest`,
`PlacementPlan`, `PlacementBudget`, `CostEstimate`, `PlacementLease`,
`LeaseSet`, `PlacementCapabilities`, `PlacementError` and `ArtifactId` already
exist in `src/lib/common/compute/placement_contracts/`. So do
`PLACEMENT_NO_SLOT`, `PLACEMENT_NO_EPOCH`, `PLACEMENT_SCHEMA_ID` and the
`residency_tier_to_u8` / `_from_u8` / `_valid` / `_is_device` encoders in that
directory's `schema.spl`.

All of them are IMPORTED. Those declarations are host-side carriers with no
byte layout; this group adds the wire layout and the rules, under `...Wire`
names where a flattened mirror was unavoidable. Two declarations of one wire
type is how lanes silently diverge.

## Conventions

Inherited unchanged from the ID-TAG lane's frozen port
`src/lib/common/structural/wire.spl`: little-endian, fixed width, no padding,
no alignment; enums as one u8; lists as a u32 count followed by elements; an
8-byte envelope of `magic u32 | version u16 | reserved u16`; decoders total and
returning an ok flag; unknown discriminants and set reserved bits HARD
REJECTED, never silently defaulted.

Magic: `SPRQ` PlacementRequest, `SPLG` LeaseGrant, `SPLS` LeaseSet, `SPPL`
PlacementPlan. `PLACE_SCHEMA_VERSION = 1`, asserted equal to the existing
`PLACEMENT_SCHEMA_ID`.

### Encode validates too

Every `encode_*` returns an EMPTY buffer when its record is not well formed,
and an empty buffer fails the envelope check, so it can never be decoded. This
follows the receipts lane, which made "no silent fallback" unrepresentable on
the wire the same way. For this group the rule that matters is the lease one: a
`Released` or `Revoked` grant carrying a live device address has no byte
encoding at all, so a stale address cannot reach a consumer even from a buggy
backend.

### Unsigned 64-bit comparison

Simple has no unsigned 64-bit scalar and `wire_get_u64` returns the
bit-identical i64, so a u64 at or above 2^63 decodes NEGATIVE. Every comparison
of a decoded u64 goes through `place_u64_lt` / `place_u64_le`, and every
overflow test through `place_u64_add_fits`, which computes the remaining room
(`-1 - a`, the bitwise complement) instead of a sum that would itself wrap.

This is the 64-bit form of the trap two earlier waves hit at 32 bits
(`offset + count <= U32_MAX` evaluated at u32 width). `GOLDEN_REQUEST_UNSIGNED_EPOCH`
pins it: its liveness interval is 1 .. 0x8000000000000000, which a signed
comparison reads as ending before it begins and would refuse to encode.

## Layouts

| Record | Bytes | Fields |
|---|---|---|
| `PlacementRequestWire` | 82 | `object_slot u32`, `generation u32`, `access u8`, `required_tiers u8`, `preferred_len u8`, `preferred u8 x7`, `persistence u8`, `deadline_present u8`, `reserved u16`, `expected_reuse_distance u32`, `device_mask u64`, `expected_first_use u64`, `expected_last_use u64`, `recompute_cost u64`, `transfer_cost_hint u64`, `affinity_group u64`, `deadline_us u64` |
| `LeaseGrant` | 32 | `object_slot u32`, `generation u32`, `lease_epoch u32`, `state u8`, `access u8`, `tier u8`, `reserved u8`, `device_address u64`, `length u64` |
| `PlacementCostWire` | 70 | the ten §21.2 fields, `synchronization_points` u32 and `confidence_milli` u16, the rest u64 |
| `PlacementPlanWire` | 142 | five `ObjectRef` pairs (`u32 slot | u32 generation`), `PlacementCostWire`, `receipt_seed` 32 raw bytes |
| `LeaseSetWire` | var | `lease_count u32`, then that many `LeaseGrant` |

`LeaseGrant` is exactly 32 bytes on purpose: §20.9 caps the hot per-object
descriptor at 32-48 bytes and a lease grant is one per resident object.

## Lease rules — the point of the group

§4.1 says an `EntityRef` is "valid only while the referenced snapshot/object
lease is valid". §20.5 says "a raw address may be used only inside the lease
epoch". Neither sentence is checkable against `PlacementLease` as declared: it
has a `lease_epoch` but no state, no rights, and no rule tying its epoch to its
address. This contract makes both decidable.

Enforced on encode AND decode:

- a LIVE grant (`Active`, `Pinned`, `InFlight`) must have
  `lease_epoch != PLACEMENT_NO_EPOCH`, non-zero rights, a non-zero
  `device_address`, a non-zero `length`, and a window that does not wrap past
  2^64;
- a DEAD grant (`Released`, `Revoked`) must have `lease_epoch ==
  PLACEMENT_NO_EPOCH`, no rights, address 0 and length 0 — a dead lease
  carrying a live address is unrepresentable;
- a `LeaseSet` must be strictly ascending by `(object_slot, generation)`, which
  gives the set ONE canonical encoding (so a receipt over it is reproducible)
  and makes a duplicate object impossible — two live leases on one object at
  different epochs is precisely the stale-address bug §30's stale-handle gate
  exists to catch.

Predicates: `lease_grant_valid_at`, `lease_grant_covers`,
`resident_view_valid_under`, `entity_ref_valid_under`,
`lease_grant_satisfies_request`, `lease_set_acquirable_from`.

**Epoch comparison is EQUALITY, never `>=`.** A lease epoch is an identity, not
an ordering: a later epoch on the same slot is a DIFFERENT lease, quite
possibly at a different address. Treating it as monotone would let a stale view
validate against a newer lease.

## Underspecified in §20 — derivations raised for ratification

The rule applied was: do not guess a vocabulary; take the minimum the
surrounding sections actually distinguish, and cite the sentence.

| Item | Where declared | Derivation |
|---|---|---|
| `LeaseState` | Nowhere. §20.5 states the rule a lease enforces but never how a lease ENDS, which is what makes §4.1 undecidable. | u8, 5 variants, NOT monotone. `Active(0)` §20.5. `Pinned(1)` and `InFlight(2)` from §20.6's planner input "pin/in-flight status" and §31's "pin/in-flight eviction prevention" gate, which name pin and in-flight as SEPARATE statuses, so two states not one. `Released(3)` from §20.4 `fn release(leases: LeaseSet)`. `Revoked(4)` from §20.3's `evictions: ObjectRef<EvictionArena>` — an eviction ends leases the holder did not release, and `PlacementError.StaleLease` plus §30's "eviction/recovery, stale-handle" gate are unreachable without a state distinguishing revocation from release. |
| `LeaseAccess` | §3.4 only: "GPU virtual-memory APIs separate address reservation, physical allocation, mapping, and **access rights**." The document adopts the explicit-residency half of that sentence and never revisits the rights half. | u8 bitset, `READ(1)`, `WRITE(2)`, bits 2..7 reserved. Exactly the two rights §20.2's `AccessPattern` already distinguishes. No third right invented — execute, atomics and coherence appear nowhere. |
| `access_pattern_required_rights` | — | The mapping tying §20.2's request field to the rights above, so an under-privileged grant is a contract rejection rather than a fault at first store. `ReadMostly` is *mostly* read, so it still writes; only `WriteOnly` drops the read right. |
| `ResidencyTierSet` wire form | §20.2 field; `semantic.spl` carries it as `[ResidencyTier]`, which has no byte layout | u8 bitset, bit *i* = the tier whose discriminant is *i* in the ALREADY-FROZEN `schema.spl` numbering. Seven tiers in one byte, bit 7 reserved. Same shape and reasoning as the ratified `MappingKindSet` and the QUERY lane's `TagIndexSet`. |
| `preferred_tiers` wire form | §20.2 declares `[ResidencyTier]` | A fixed 7-entry `u8` array plus a `preferred_len u8`. Seven because a strict preference order over the 7-tier set cannot be longer. Unused entries are `0xff`, NOT 0 — 0 is a valid discriminant (`DeviceLocal`), so a zero filler would read as a real preference. Fixed width keeps the whole request record byte-addressable for the SoA arena §20.4's `PlacementRequestArenaRef` implies. |
| `preferred ⊆ required` | — | Not stated, but `required_tiers` reads as the set that satisfies the request and `preferred` as an order among them. Enforcing containment makes a plan that lands an object in a tier the request did not accept detectable at the contract boundary. **Flagged for ratification**: if `preferred` was intended to be able to name a tier outside `required`, this check must be dropped before any planner ships. |
| `DeviceMask` bit vocabulary | §20.2 `device_mask`, §21 `allowed_devices`; `semantic.spl` has it as an opaque `u64` with no bit meanings | **ADOPTED VERBATIM from the EXEC lane** (`structural/execution/profile_types.spl`, `2d06051444e`): `CPU_SCALAR(1)`, `CPU_SIMD(2)`, `GPU(4)`, `STORAGE(8)`, remaining 60 bits reserved and hard-rejected, zero invalid. Placement is arguably the natural owner of device semantics, but §20.2's `device_mask` and §21's `allowed_devices` are THE SAME MASK, and a second vocabulary for one wire field is exactly the divergence the freeze exists to prevent. Placement imports `device_mask_valid` / `device_mask_has` rather than restating them. |
| `device_mask` must carry the GPU bit when a device tier is required | §20.2 field, §20.4 `PlacementCapabilities.device_mask` | `DeviceLocal` and `DeviceShared` are VRAM tiers, so a request requiring one while not permitting the GPU is satisfiable by no backend. This is stricter than "non-zero" and is only expressible BECAUSE the bit vocabulary above was adopted rather than left opaque. |
| `expected_first_use <= expected_last_use` | §20.6 "liveness intervals" | An interval that ends before it begins is not an interval. Compared UNSIGNED. |
| `deadline` absence | §20.2 `deadline: Deadline?` | `deadline_present u8` plus `deadline_us u64`, and `deadline_us` must be 0 when absent. Without the second half a decoder could not tell "no deadline" from "a deadline at timestamp 0", and the record would have two encodings. |
| `PlacementPlan` arena absence | §20.3 declares five `ObjectRef` fields with no optionality | `PLACEMENT_NO_SLOT` means the plan has no arena of that kind (a plan with nothing to evict is ordinary), and the generation must then be 0 so absence has one encoding. The `leases` arena is the one MANDATORY field, because §20.4's `acquire(plan) -> Result<LeaseSet, ...>` is unconditional — a plan naming no lease arena can never be acquired. |
| `receipt_seed` wire form | §20.3 `Hash256`; `semantic.spl` carries it as `text` | 32 raw bytes on the wire, spelled host-side as 64 LOWERCASE hex characters — the same digest spelling `placement_contracts/storage.spl` already requires of an `ArtifactId`. Uppercase is rejected, not folded: two spellings of one hash would give one plan two encodings. |
| `confidence_milli <= 1000` | §21.2 field name only | Per-mille. A value above 1000 is not a probability, and a planner reading one as a weight would over-trust the estimate. |

### Settled, not deferred: CostEstimate overlaps the EXEC lane

§20.3 embeds `CostEstimate` BY VALUE, so a `PlacementPlan` is unencodable
without freezing its layout. Its 70-byte layout is therefore frozen here.
**The EXEC lane's "ExecutionProfile and capability vocabulary" group must adopt
this layout rather than mint a second one.** Note there are already TWO
`CostEstimate` declarations in tree — `compute/placement_contracts/planner.spl`
(the §21.2 one, which this group encodes and bridges to via
`placement_cost_from_estimate`) and `structural/execution/contracts.spl` (a
LAYOUT-lane estimate with entirely different fields). That collision predates
this wave and is reported, not resolved here.

### Still open after this wave

Not frozen here because they are handle/runtime types outside the wire scope:
`PlacementBackend`, `PlacementCapabilities`, `PlacementBudget`,
`ReservationArena` / `TransferArena` / `EvictionArena` / `PrefetchArena` /
`LeaseArena` element formats, `TransferReceipt`, `CheckpointReceipt`,
`RecoveryReceipt`, `PlacementSnapshot`, `retain_score` policy.

**Reported gap, NOT invented here:** the architecture specifies no lease
LIFETIME. There is no duration, no renewal, and no rule saying who may move a
grant from `Active` to `Revoked` or when. This contract freezes the wire slot
(`state`) and the vocabulary, so revocation is representable and checkable, but
the revocation POLICY — who revokes, on what event, and whether a holder is
notified — is left to the PLACE lane to ratify. A `Pinned` or `InFlight` grant
must not be revoked by an eviction plan (§20.6, §31), which is the only
constraint the document actually states.

## Compatibility and versioning policy

Same policy as waves 0a/0b/0c/0d:

- `PLACE_SCHEMA_VERSION = 1`, and it must equal `PLACEMENT_SCHEMA_ID`. A
  decoder rejects any version it does not equal; a version mismatch is a
  rejection, not a negotiation (§12.6).
- Enum discriminants are wire values. New variants take the next free number; a
  discriminant is never reused or renumbered.
- Adding an 8th `ResidencyTier`, a 6th `AccessPattern`, a 5th
  `PersistencePolicy`, a 6th `LeaseState` or a 3rd `LeaseAccess` right is a
  **breaking** change requiring a version bump, because the golden vectors pin
  the maximum discriminants and the reserved masks.
- Reserved bits and reserved bytes must be zero and are hard-rejected when set.
- The record lengths (`PLACEMENT_REQUEST_LEN = 82`, `LEASE_GRANT_LEN = 32`,
  `PLACEMENT_COST_LEN = 70`, `PLACEMENT_PLAN_LEN = 142`) are part of the
  contract; changing one is a version bump.
- The lease rules are part of the contract. Relaxing any of them — permitting a
  dead grant to carry an address, permitting an unordered `LeaseSet`, or
  comparing lease epochs with `>=` — is a breaking change, because consumers are
  entitled to treat a decoded grant as safe to dereference.

## Golden vectors

`test/fixtures/structural/placement_golden_v1.spl` (Simple) and
`test/fixtures/structural/placement_golden_v1.sdn` (language-neutral mirror,
for a Rust/C++ bridge or an external validator).

Every hex string was derived **by hand from the layout tables above**, not
captured from encoder output. The spec asserts encoder output EQUALS the vector,
which is the direction that catches a symmetric encode/decode defect — a round
trip alone passes one straight through.

Verified during this wave: swapping `device_address` and `length` in BOTH the
encoder and the decoder left every round-trip assertion green (73 passed) and
failed exactly the three exact-byte lease assertions.

## Cross-lane notes

- **`DeviceMask` bits are the EXEC lane's**, adopted unchanged (see the table).
  If placement ever needs device semantics the four cost channels cannot
  express, that is a joint version bump of both groups, not a second mask.
- **`CostEstimate` has TWO in-tree declarations** —
  `compute/placement_contracts/planner.spl` (the §21.2 one this group encodes)
  and `structural/execution/contracts.spl` (a LAYOUT-lane record with entirely
  different fields). Same name, different meaning, in a directory this group
  imports from. The collision predates this wave and is reported, not resolved
  here.
