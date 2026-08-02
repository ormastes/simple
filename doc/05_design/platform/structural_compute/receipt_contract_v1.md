# StageReceipt / VerificationReceipt contract v1 (FROZEN)

Artifact group 7 of the eleven listed in architecture §26
(`doc/04_architecture/compiler/mdsoc/mdsoc_plus_tagged_structural_compute_architecture.md`):

```text
StageReceipt and VerificationReceipt
```

Owned by the EXEC lane (§27). Conventions are inherited unchanged from wave 0a
(`identity_tagmap_contract_v1.md`) and wave 0b (`mapping_contract_v1.md`):
little-endian fixed-width fields, no padding, no alignment, `u8` enum
discriminants, the 8-byte record envelope, total decoders, and **hard rejection
of any unknown discriminant or set reserved bit**.

| Deliverable (§26) | Where |
|---|---|
| language-neutral binary/SDN schema | §2–§5 below, `test/fixtures/structural/receipt_golden_v1.sdn` |
| Simple types | `src/lib/common/structural/receipt/receipt_types.spl` |
| Rust/C++ bridge types | not shipped — see §9 |
| CPU reference serializers/deserializers | `src/lib/common/structural/receipt/receipt_codec.spl` |
| golden vectors | `test/fixtures/structural/receipt_golden_v1.{spl,sdn}` |
| compatibility/versioning policy | §8 |

Gate spec: `test/01_unit/common/structural/receipt_contract_spec.spl`.

---

## 1. What this group freezes, and what it deliberately does not

### 1.1 Types NOT redeclared

`StageReceipt` **already existed** before this freeze, in
`src/lib/common/structural/execution/contracts.spl`, aliased as `LayoutReceipt`
and read by roughly twenty modules. It is **imported, never redeclared**. Two
declarations of one wire record is how two lanes come to disagree about a field
while both report success; the MAP lane met the identical situation with
`MappingKind` and resolved it the same way.

`ExecutionMode`, `StageId`, `BackendId` and `Hash256` likewise already exist in
`src/lib/common/compute/placement_contracts/semantic.spl`. `ExecutionMode`
there carries exactly §21's three variants in exactly §21's order, so it *is*
the frozen enum and is imported. `structural/resolve/style_link_receipts.spl`
already imports that module by the same path, so this is an established edge,
not a new cross-lane dependency.

### 1.2 Deferred types: which one was actually ours

§6.4 of the architecture defers three handle/view types and says explicitly why:

> Three types in these signatures are deliberately **not** frozen and remain
> tracked open gaps: `MappingShardRef` (`finish()`, and a field of
> `StageReceipt` and `VerificationReceipt`), `SourceOriginSet`
> (`trace_to_source`) and `EntitySetView` (also used by §5's tag index port).

Resolution:

| Type | Verdict | Why |
|---|---|---|
| `MappingShardRef` | **FROZEN HERE** | §6.4 states in so many words that it is *a field of StageReceipt and VerificationReceipt*. It cannot be left open without leaving a hole in this group's records. |
| `SourceOriginSet` | **NOT frozen — ownership genuinely ambiguous, reported** | It is the return type of `MappingGraph::trace_to_source` and is referenced by **no receipt field anywhere in §21**. It belongs to MAP or to QUERY, and nothing in §26/§27 decides between them. Guessing would repeat the pre-emption §6.4 was written to avoid. |
| `EntitySetView` | **Frozen elsewhere, not here** | Shared with the tag index port (§5) and the QueryIR group, which froze it in `query_contract_v1.md`: 13 bytes, `object_slot u32 | offset u32 | count u32 | order u8`, magic `SQSV`. Round-trip verified against the implementation 2026-08-02. |

---

## 2. THE CONTRACT DEFECT — reported loudly, per the brief

**§21.3's `StageReceipt` cannot express the distinction the whole lane plan
depends on.** This is the headline finding of this freeze.

§21.3 as written is:

```simple
struct StageReceipt:
    stage: StageId
    backend: BackendId
    mode: ExecutionMode
    input_root: Hash256
    output_root: Hash256
    item_count_in: u64
    item_count_out: u64
    bytes_read: u64
    bytes_written: u64
    fallback_count: u32
    malformed_count: u32
    overflow_flags: u64
    elapsed_us: u64
    deterministic_hash: Hash256
```

§21.4 lists eight fallback reasons and asserts the rule:

> A fallback does not silently change semantics. It emits a reason and
> preserves stable ordering and hashes.

**The struct has nowhere to put that reason.** It carries `fallback_count` — a
number — and nothing else about *why*. Worse, one of §21.4's eight lines is
"cost-model chooses CPU", which is a *planned* selection implementing §21.2's
rule ("the scheduler chooses GPU only when expected total cost ... beats the CPU
path"), while the other seven are *forced degradations*. Under §21.3:

- cost-model CPU selection → `mode = CpuReference`, `fallback_count = 1`
- GPU device loss → `mode = CpuReference`, `fallback_count = 1`

**Byte-for-byte identical.** A working cost model and a lost GPU produce the
same receipt. `cpu_selected` is not distinguishable from `gpu_fallback`, which
is exactly the property the lane plan says the receipts must carry.

There is a second, quieter hole: §21.3 records the mode that *ran* but not the
mode that was *requested*. Even with a reason field, `mode = CpuReference` on a
stage that was never asked to use a device is not a fallback at all, and nothing
in the record says which case it is.

### 2.1 The fix, and why it is not an invention

Three fields are added to the frozen wire form:

| Field | Purpose |
|---|---|
| `requested_mode: ExecutionMode` | what `ExecutionProfile.mode` asked for |
| `candidate_backend: BackendId` | the backend the cost model first considered |
| `fallback_reason: StageFallbackReason` | §21.4's list as a closed `u8` enum |

This is corroborated rather than invented: **the in-tree `StageReceipt` had
already grown `candidate_backend` and `fallback_reason` fields before this
freeze**, because the layout lane needed them in practice. That is evidence
§21.3 is short, not that this lane is over-reaching. `requested_mode` is the one
addition with no in-tree precedent, and it is raised as ratification item **R1**
(§7) precisely for that reason.

With them, the two cases separate mechanically:

```text
cost-policy CPU   requested HybridVectorGpu, ran CpuReference,
                  reason = CostModelSelectedCpu  -> stage_fallback_is_policy
forced fallback   requested HybridVectorGpu, ran CpuReference,
                  reason = DeviceLost (etc.)     -> stage_fallback_is_forced
```

and the golden vectors `GOLDEN_STAGE_RECEIPT_CPU_SELECTED` and
`GOLDEN_STAGE_RECEIPT_GPU_FALLBACK` are **byte-for-byte identical except for
one byte at offset 14**, which the spec asserts directly.

### 2.2 No-silent-fallback is enforced, not merely representable

A representation that *can* express the reason is not the same as one that
*requires* it. `stage_receipt_selection_consistent` makes the §21.4 sentence a
wire-level rule:

- a receipt whose mode differs from the requested mode and reports reason
  `None` is **rejected** — that is precisely the silent fallback;
- a receipt whose mode matches and yet names a reason is **rejected**;
- a mode or reason spelling this build does not sanction is **rejected**.

The rule runs on **encode as well as decode**, so a producer cannot put a silent
fallback on the wire at all. `encode_stage_receipt` returns an empty buffer for
such a receipt rather than bytes no decoder will accept.

---

## 3. Enum vocabularies

### 3.1 `StageFallbackReason` (u8, 9 discriminants)

§21.4's eight lines in the order printed there, plus `None` at 0.

| # | Variant | Class |
|---|---|---|
| 0 | `None` | neither |
| 1 | `UnsupportedFeature` | forced |
| 2 | `ResourceBudgetExceeded` | forced |
| 3 | `QueueOverflow` | forced |
| 4 | `MalformedInput` | forced |
| 5 | `VerificationMismatch` | forced |
| 6 | `DeviceLost` | forced |
| 7 | `StorageError` | forced |
| 8 | `CostModelSelectedCpu` | **policy** |

`None = 0` is **derived, not invented**: §21.3 permits `fallback_count == 0`, so
a receipt that did not fall back still has to put something in the slot, and a
sentinel-free field would force a reader to guess. Zero-means-absent matches
`MAPPING_FLAG_NONE` in wave 0b.

Named `StageFallbackReason`, **not** `FallbackReason`, because
`src/compiler/80.driver/compilability.spl` already declares an unrelated
`FallbackReason` enumerating JIT-to-interpreter demotion causes. The two
vocabularies must never be conflated — one is about which engine executes Simple
code, this one about whether a compute stage ran on the device it was planned
for. Reusing the name would let a future merge silently unify them.

### 3.2 `VerificationPolicy` (u8, 5 discriminants) — see ratification item V1

### 3.3 `VerificationOutcome` (u8, 4 discriminants)

`NotRun`, `Match`, `Mismatch`, `OracleUnavailable`. Only `Match` is clean:
`verification_outcome_is_clean` returns **false** for `NotRun` and for
`OracleUnavailable`, because treating "we did not check" as "it was fine" is the
silent pass this lane exists to prevent.

---

## 4. Wire layouts

All little-endian, fixed width, no padding. Envelope = `magic u32` (4 ASCII, LE)
| `version u16` | `reserved u16` (== 0). Text fields are `u32 length` followed by
that many ASCII bytes (wire.spl's list rule); non-ASCII is a hard reject.

```text
MappingShardRef  "SRMS"  52  snapshot SnapshotId 28 | shard_index u32 4
                             | edge_count u32 4 | content_hash Hash128 16

StageReceipt     "SRSR"  63 + texts
                             contract_version u32 | requested_mode u8
                             | mode u8 | fallback_reason u8
                             | item_count_in u64 | item_count_out u64
                             | bytes_read u64 | bytes_written u64
                             | fallback_count u32 | malformed_count u32
                             | overflow_flags u64 | elapsed_us u64
                             | stage text | backend text
                             | candidate_backend text | input_hash text
                             | output_hash text | deterministic_hash text

VerificationReceipt "SRVR" 91 + texts
                             contract_version u32 | mode u8 | policy u8
                             | outcome u8 | checked_count u64
                             | mismatch_count u64 | first_mismatch EntityRef 8
                             | elapsed_us u64 | origins MappingShardRef 52
                             | stage text | backend text
                             | result_hash text | oracle_hash text
```

`MappingShardRef` is embedded **unframed** inside `VerificationReceipt`, exactly
as `MappingShard` embeds bare `MappingEdge` bodies in wave 0b.

### 4.1 Fields the wire does not carry

The in-tree `StageReceipt` has ten further fields (`visited_island_ids`,
`converged`, `iterations`, `cpu_us`, `gpu_us`, `submitted`, `synchronized`,
`device_readback`, `oracle_verified`). These are **layout-lane scratch and are
NOT part of this contract**: freezing them would freeze one lane's internals into
a cross-lane format. Decode reconstructs exactly the wire projection and returns
those fields at documented zero defaults, which is why the spec compares
receipts with `stage_receipt_wire_equal` rather than field-wise.

---

## 5. `VerificationReceipt` — defined here for the first time

`VerificationReceipt` is **used in two architecture signatures and defined
nowhere**:

- §21.1 `fn verify(result: Result, policy: VerificationPolicy) -> VerificationReceipt`
- §19.5 `fn verify(result: LayoutFragmentArenaRef, oracle: LayoutSnapshotRef?) -> VerificationReceipt`

Nothing in the architecture says what it contains. Every field below is traced
to the text that forces it; this is the type with the least prose behind it and
the most need of freezing.

| Field | Derivation |
|---|---|
| `stage`, `backend`, `mode` | mirrors `StageReceipt`'s identifying head so a verification receipt joins to the stage receipt it checks without a separate correlation id |
| `policy` | §21.1's parameter |
| `outcome` | §21.4 names "verification mismatch" as a fallback reason, so success and failure are distinguished |
| `checked_count`, `mismatch_count` | §21.3's counter style; needed for `Sampled` to mean anything |
| `first_mismatch: EntityRef` | §21.4 requires a fallback to "emit a reason"; a mismatch reason without a locus is not actionable |
| `result_hash`, `oracle_hash` | §21.3's `deterministic_hash` style; §29's gate is cross-mode deterministic output |
| `origins: MappingShardRef` | §6.4 states it is a field of this record |
| `elapsed_us` | §21.3 |

### 5.1 A verification receipt cannot lie

`verification_receipt_consistent` rejects, on encode and decode:

- `Mismatch` with `mismatch_count == 0` — reads as a pass to anything counting;
- a clean outcome with a non-zero mismatch count;
- `mismatch_count > checked_count`;
- `NotRun` claiming to have checked items;
- an oracle hash present under a policy that consults no oracle.

---

## 6. Ambiguities resolved, with derivations

Each was frozen as a wire **slot** with the minimum vocabulary the surrounding
sections actually distinguish, rather than guessed silently.

| # | Item | Resolution | Derived from |
|---|---|---|---|
| A1 | `StageId` / `BackendId` width | length-prefixed ASCII text | §21.3 names them and defines neither; the only declaration in the repository is `class StageId: value: text` in `placement_contracts/semantic.spl`. See **R2**. |
| A2 | `Hash256` width | length-prefixed ASCII text (hex) | same — the only in-repo `Hash256` is `class Hash256: value: text`, and the in-tree `StageReceipt` stores `input_hash: text`. See **R2**. |
| A3 | `ExecutionMode` text spellings | `cpu_reference`, `hybrid_vector_gpu`, `resident_gpu` | §21.5's mode-matrix column names and §30's worked examples, which literally write `fallback: cpu_reference`. |
| A4 | `StageFallbackReason` vocabulary | §21.4's eight lines + `None` | §21.4 verbatim; `None` derived from §21.3 permitting `fallback_count == 0`. |
| A5 | `VerificationPolicy` vocabulary | `Off`, `DeterministicHash`, `Sampled`, `Full`, `OracleCompare` | See **V1** below. |
| A6 | `VerificationOutcome` vocabulary | `NotRun`, `Match`, `Mismatch`, `OracleUnavailable` | §21.4's "verification mismatch"; §19.5's oracle parameter is optional, so an oracle can be absent when one was requested. |
| A7 | `MappingShardRef` contents | `snapshot`, `shard_index`, `edge_count`, `content_hash` | §6.4 calls it a handle; a handle that cannot be checked against the shard it names silently reads another stage's provenance, which §6.5 forbids ("a pass cannot silently drop origins"). |
| A8 | `MappingShardRef` hash width | `Hash128`, reused from ID-TAG | introducing a second content-hash width across the structural contracts would be a divergence with no source in the text. |

### V1 — `VerificationPolicy` variant derivations

`VerificationPolicy` is named in §21's `ExecutionProfile` and in §21.1's `verify`
signature, enumerated nowhere, and declared nowhere in the repository.

| Variant | Sentence that forces it |
|---|---|
| `Off` | §21 makes `verification` a field of `ExecutionProfile`, so asking for none must be expressible. |
| `DeterministicHash` | §21.3 already carries `deterministic_hash`, and §29's gate is "cross-mode deterministic output" — comparing that one hash is a distinct, cheap policy. |
| `Sampled` | §20.8/§20.9 forbid per-node metadata and per-node cost; verifying every item contradicts them, so a partial policy must exist. |
| `Full` | the §29 gate has to be reachable exactly. |
| `OracleCompare` | §19.5's `verify(result, oracle: LayoutSnapshotRef?)` takes an **optional** oracle and §24's risk table lists "Clang oracle/fallback" — an oracle-present policy is therefore distinguished from every oracle-absent one. |

---

## 7. Raised for ratification

**R1 — add `requested_mode` to `StageReceipt`.** The wire carries it; the
in-tree struct does not, so `encode_stage_receipt` takes it as a parameter and
`StageReceiptResult` returns it as a field. Without it, `mode = CpuReference`
cannot be told from a CPU run nobody asked to accelerate, and §2's whole
distinction collapses. This lane did not edit a struct twenty modules read;
ratifying the field is the clean fix.

**R2 — decide whether `StageId` / `BackendId` / `Hash256` are names or numbers.**
§21.3 implies opaque dense ids; the only in-repo declarations are text wrappers.
This freeze follows the repository. If a dense numeric registry was intended,
that is a schema-version bump, not an additive change.

**R3 — §21.3 should absorb `fallback_reason` and `candidate_backend`.** Both
already exist in the in-tree struct and are now on the wire. The architecture
text should stop omitting them, so the next lane reading §21.3 does not
reconstruct the same hole.

**R4 — existing call sites write free-form reason text.** `fallback_reason` is
declared `text` and call sites write ad-hoc strings (`glsl_reason`,
`unavail_reason`, `not_found_reason`). The frozen codec **rejects** any spelling
outside §21.4's list. Those sites need migrating to the sanctioned vocabulary.
This is a real, currently-unmet migration, not a theoretical one.

**R5 — `SourceOriginSet` ownership is undecided.** §6.4 defers it, §21 never
references it from a receipt, and §26/§27 do not assign it. MAP and QUERY both
have a claim. Reported rather than guessed.

---

## 8. Compatibility and versioning policy

- `RECEIPT_SCHEMA_VERSION = 1` is **frozen**. A reader MUST reject any other
  version rather than negotiate (`wire_check_envelope`, per §12.6).
- Adding a `StageFallbackReason`, `VerificationPolicy` or `VerificationOutcome`
  variant is a **breaking** change requiring a version bump, because readers
  hard-reject unknown discriminants by design. This is the same consequence
  wave 0b recorded for an 18th `MappingKind`.
- Adding a trailing field is **also breaking**: decoders reject trailing bytes,
  so there is no silent-extension path. Deliberate — a silent-extension path is
  a silent-divergence path.
- The three magics (`SRSR`, `SRVR`, `SRMS`) are permanent; a new record type
  takes a new magic.
- The golden vectors are the contract. They are never edited in place; a change
  that alters them is a version bump.

## 9. Rust/C++ bridge types

Not shipped: no caller exists at this revision. The byte layout in §4 and the
`.sdn` golden vectors let the owning bridge lane build and validate one without
running Simple, which is the same call wave 0a and 0b made.
