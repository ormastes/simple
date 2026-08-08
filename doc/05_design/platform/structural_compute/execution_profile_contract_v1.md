# ExecutionProfile and capability vocabulary — frozen contract v1

Architecture: `doc/04_architecture/compiler/mdsoc/mdsoc_plus_tagged_structural_compute_architecture.md`
§21 (execution profile), §21.1 (`StageBackend.capabilities`), §21.2 (cost
estimate), §21.4 (fallback rules), §21.5 (cross-domain mode matrix), §20.2
(`device_mask`), §20.7 (storage backends), §26 (contract freeze, artifact
group 9: "ExecutionProfile and capability vocabulary").

Simple types: `src/lib/common/structural/execution/profile_types.spl`
CPU reference codec: `src/lib/common/structural/execution/profile_codec.spl`
Golden vectors: `test/fixtures/structural/execution_profile_golden_v1.{spl,sdn}`
Freeze gate: `test/01_unit/common/structural/execution_profile_contract_spec.spl`

This document is normative for the byte layout. The golden vectors were derived
by hand from this document and the encoder is asserted against them, not the
other way round.

---

## 1. What this group does NOT declare

Four names in §21 already exist in the tree. All four are **imported**;
redeclaring a wire type is how two lanes come to disagree about a field while
both report success.

| Name | Already lives in | Treatment |
|---|---|---|
| `ExecutionMode` | `common/compute/placement_contracts/semantic.spl` | imported; carries §21's three variants in §21's order |
| `DeviceMask` | `common/compute/placement_contracts/semantic.spl` | imported; it is `class DeviceMask: bits: u64` with **no defined bit meanings anywhere**, so this group freezes the *bit vocabulary*, not the type |
| `VerificationPolicy` | `common/structural/receipt/receipt_types.spl` | imported; frozen by the receipts wave with §21.1's five levels |
| `StageReceipt` | `common/structural/execution/contracts.spl` | not touched; the receipts wave already froze its wire form |

### 1.1 Why the record is named `StageExecutionProfile`

`ExecutionProfile` — the name — is already taken **in this very directory**
(`contracts.spl`) by an unrelated record. That one carries `cpu_us`,
`gpu_kernel_us`, `scheduling_us`, `transfer_us_per_kib`, `sync_us`: **measured
cost**. It is aliased `LayoutExecutionProfile` and read by ~20 modules. §21's
`ExecutionProfile` carries determinism, budgets, targets and policies, and
shares **not one field** with it beyond `mode`.

Per the freeze rule "if a name collides with an unrelated type, pick a distinct
one", §21's record is frozen as **`StageExecutionProfile`**, matching the
frozen `Stage*` family (`StageReceipt`, `StageFallbackReason`) and §21.1's own
`estimate(request, profile: ExecutionProfile)`, which is a per-stage call.
`contracts.spl` is neither edited nor redeclared.

The same reasoning produced `StageFallbackPolicy` rather than `FallbackPolicy`
(the compiler layer's `OffloadFallbackPolicy` is a different, coarser thing).

### 1.2 Deliberately NOT frozen — reported for ratification

`CapabilitySet` (§12.6, `ClangAdapterCapability.supported_features`). The
architecture never enumerates a single member of it, and `CapabilitySet` is
already a kernel type (`src/os/kernel/types/capability_types.spl`). It belongs
to the Clang lane. Guessing its members would be inventing vocabulary.

---

## 2. Wire conventions

Shared with every other frozen structural group (`common/structural/wire.spl`):

- little-endian, fixed width, **no padding, no alignment**;
- 8-byte envelope: `magic u32 (4 ASCII, LE) | version u16 | reserved u16 (== 0)`;
- text: `u32` length then that many printable-ASCII bytes;
- **unknown discriminants and set reserved bits are HARD-REJECTED**, never
  coerced to a default;
- decoders are total — they return an `ok` flag rather than trapping;
- scalars are fixed-width unsigned, little-endian; writers mask to width.

§21 spells budgets and targets `u64`. Simple has no unsigned 64-bit scalar, so
they are carried as `i64` and **required to be non-negative**: a negative value
is the bit pattern of a budget above 2^63, which no real budget is, so treating
it as an error catches sign bugs instead of encoding them.

Magics: `SXEP` = `StageExecutionProfile`, `SXSC` = `StageCapabilities`. Both
differ from the receipt family (`SRSR`/`SRVR`/`SRMS`), so a buffer handed to the
wrong decoder is rejected by the envelope rather than misread.

---

## 3. Capability vocabulary and its derivation

Nothing below is invented. Each entry names the sentence it comes from.

### 3.1 Device-mask bits (over the imported `DeviceMask.bits`)

The architecture never lists device classes. It does distinguish exactly four
kinds of executor, by giving each its own cost channel in §21.2's
`CostEstimate`. A cost model that budgets a channel separately must be able to
forbid that channel separately.

| Bit | Name | Derived from |
|---|---|---|
| 0 (1) | `cpu_scalar` | §21.2 `cpu_work`; §21.5 "canonical scalar" |
| 1 (2) | `cpu_simd` | §21.2 `simd_work`; §21.5 "SIMD/GPU lex/structure" |
| 2 (4) | `gpu` | §21.2 `gpu_work` |
| 3 (8) | `storage` | §21.2 `ssd_read_bytes`/`ssd_write_bytes`; §20.7 |

Bits 4..63 are RESERVED and hard-rejected. A mask of `0` is malformed: it
permits no executor, so nothing could ever run under it.

### 3.2 Mode-mask bits

Bit `i` means `ExecutionMode` discriminant `i`, so no second ordering is
introduced: `cpu_reference` 1, `hybrid_vector_gpu` 2, `resident_gpu` 4.

### 3.3 `StageFallbackPolicy`

§21.4 enumerates eight fallback *reasons* (frozen by the receipts wave) but
never says who is *allowed* to fall back. The only ladder the architecture
states is in `src/compiler/00.common/structural_contracts/offload_profile.spl`:

```
hybrid -> cpu_reference;  resident -> hybrid -> cpu_reference
```

That ladder has exactly three stopping points, which is exactly this vocabulary
and no more:

| Value | Name | Meaning |
|---|---|---|
| 0 | `forbid` | raise instead of degrading |
| 1 | `allow_hybrid` | `resident_gpu` may degrade to `hybrid_vector_gpu`, never to CPU |
| 2 | `allow_cpu` | the full ladder, down to `cpu_reference` |

An unknown discriminant decodes to `forbid` — the **safe** rung. It must never
decode to a value permitting more degradation than the producer wrote.

### 3.4 `StorageCapabilityTier`

§20.7 verbatim, in the order printed there, carrying the status §20.7 assigns:
`staged` 0 (the "mandatory portable backend"), `direct` 1 ("optional
capability"), `device_initiated` 2 ("experimental capability").

Mask bits 1/2/4. A non-zero storage mask **must** include `staged`: a backend
advertising `direct` or `device_initiated` without the portable path has no
fallback when the optional facility is unavailable, which is the silent
degradation §21.4 forbids. Zero is legal — a stage that touches no storage
claims no tier.

### 3.5 `StageCapabilities`

§21.1 declares `fn capabilities() -> StageCapabilities` and never the record.
The minimum a planner needs to decide whether a profile can be honoured
*without degrading* is one answer per question the profile asks:

| Field | Answers the profile's | From |
|---|---|---|
| `supported_modes` | `mode` | §21.5's matrix cells |
| `device_mask` | `allowed_devices` | §20.2, §21.2's channels |
| `max_verification` | `verification` | §21.1's verify policy |
| `deterministic` | `deterministic` | §21's profile field |
| `storage_tiers` | — | §20.7 |
| `backend` | matches a receipt's `backend`/`candidate_backend` | §21.3 |

No field without a question behind it was added.

---

## 4. Byte layout

### 4.1 `StageExecutionProfile` — 8 envelope + 48 body = 56 bytes

| Offset | Width | Field |
|---|---|---|
| 0 | u32 | `contract_version` (== 1) |
| 4 | u8 | `mode` (`ExecutionMode` discriminant) |
| 5 | u8 | `deterministic` (exactly 0 or 1) |
| 6 | u8 | `fallback` (`StageFallbackPolicy`) |
| 7 | u8 | `verification` (`VerificationPolicy`) |
| 8 | u64 | `host_memory_budget` |
| 16 | u64 | `device_memory_budget` |
| 24 | u64 | `latency_target_us` |
| 32 | u64 | `throughput_target` |
| 40 | u64 | `allowed_devices` (device-mask bits) |

### 4.2 `StageCapabilities` — 8 envelope + 16 head + text

| Offset | Width | Field |
|---|---|---|
| 0 | u32 | `contract_version` (== 1) |
| 4 | u8 | `supported_modes` (mode-mask bits) |
| 5 | u8 | `storage_tiers` (storage-mask bits) |
| 6 | u8 | `max_verification` (`VerificationPolicy`) |
| 7 | u8 | `deterministic` (exactly 0 or 1) |
| 8 | u64 | `device_mask` (device-mask bits) |
| 16 | text | `backend` (u32 length, then ASCII bytes) |

Trailing bytes are rejected: the record is exactly its declared extent.

---

## 5. Invariants — enforced on ENCODE as well as decode

An encoder that accepts what its decoder refuses is how a contract rots from
one side. Both directions call the same gate.

1. **version_exact** — `contract_version` and envelope version must both be 1.
   A version mismatch is a rejection, not a negotiation (§12.6).
2. **unknown_discriminant** — `mode`, `fallback`, `verification` out of range
   is a hard reject.
3. **reserved_bits** — any set reserved bit in the device, mode or storage mask
   is a hard reject.
4. **bool_is_zero_or_one** — `deterministic` is exactly 0 or 1. It gates
   reproducibility claims, so a byte of 2 must not quietly become `true`.
5. **device_mask_nonempty** — `allowed_devices == 0` is malformed.
6. **mode_device_consistent** — `hybrid_vector_gpu` or `resident_gpu` requires
   the `gpu` bit (§21.5: both are device columns).
7. **fallback_reachable_cpu** — `allow_cpu` requires the `cpu_scalar` bit; a
   permitted rung must be a reachable one.
8. **fallback_hybrid_from_resident** — `allow_hybrid` is legal only from
   `resident_gpu`. Elsewhere there is no hybrid step below, so it would be a
   second spelling of `forbid`; rejecting it keeps one policy to one spelling.
9. **budgets_non_negative** — budgets and targets `>= 0`, and the two memory
   budgets must not overflow when summed. **The sum is checked by the SIGN of
   the `i64` result, never against a width-limited constant** — `a + b <= MAX`
   on two same-width unsigned fields evaluates at that width and wraps, which
   is the trap that cost earlier waves real time.
10. **storage_staged_mandatory** — a non-zero storage mask must include
    `staged` (§20.7).
11. **capabilities_self_consistent** — a GPU mode bit requires the `gpu` device
    bit; a `cpu_reference` mode bit requires the `cpu_scalar` bit; `backend` is
    non-empty ASCII.
12. **exact_length** — trailing bytes rejected.

### 5.1 Why invariant 6 is the "no silent fallback" guarantee

The receipts wave froze `requested_mode` / `candidate_backend` /
`fallback_reason` so a forced degradation is distinguishable from a cost-policy
CPU choice **after** the fact. This group is the **before** half.

A profile whose requested mode its own device mask forbids is *unsatisfiable*,
and the only way to "honour" it is to run somewhere else without saying so.
Such a profile **encodes to an empty buffer** — it cannot reach a backend, so
it can never become an unexplained `cpu_reference` receipt. Rejecting it here
is what makes the receipt-side guarantee reachable rather than aspirational.

`profile_requires_error_on_unsatisfied` states the other half: under `forbid`,
a planner that cannot honour the request MUST raise.

---

## 6. Rust / C++ bridge types

The layout is fixed-width, little-endian and unpadded, so a bridge is a plain
struct plus explicit reads — **no `#[repr(C)]` struct may be memcpy'd over the
buffer**, because C alignment would insert padding this format does not have.

```rust
pub const SXEP_MAGIC: u32 = u32::from_le_bytes(*b"SXEP");
pub const SXSC_MAGIC: u32 = u32::from_le_bytes(*b"SXSC");
pub const CONTRACT_VERSION: u16 = 1;

pub const DEV_CPU_SCALAR: u64 = 1;
pub const DEV_CPU_SIMD:   u64 = 2;
pub const DEV_GPU:        u64 = 4;
pub const DEV_STORAGE:    u64 = 8;
pub const DEV_KNOWN:      u64 = 15;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum StageFallbackPolicy { Forbid = 0, AllowHybrid = 1, AllowCpu = 2 }

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum StorageCapabilityTier { Staged = 0, Direct = 1, DeviceInitiated = 2 }

pub struct StageExecutionProfile {
    pub contract_version: u32,
    pub mode: u8,
    pub deterministic: bool,
    pub fallback: StageFallbackPolicy,
    pub verification: u8,
    pub host_memory_budget: u64,
    pub device_memory_budget: u64,
    pub latency_target_us: u64,
    pub throughput_target: u64,
    pub allowed_devices: u64,
}
```

A bridge decoder MUST reproduce every invariant in §5. A bridge that only
round-trips is not conformant: the conformance test is the golden vectors in
`execution_profile_golden_v1.sdn`, which is plain hex and needs no Simple
parser.

---

## 7. Compatibility and versioning policy

| Change | Class | Rule |
|---|---|---|
| unknown envelope version | — | reject; never assume compatibility (§12.6) |
| unknown discriminant | — | reject; never coerce to a default |
| new device / mode / storage bit, or new enum discriminant | MINOR | ships as version 2. A v1 reader hard-rejects it (it is a reserved bit or an out-of-range discriminant), so it can never be silently misread; a v2 reader still accepts v1 buffers. Reserved bits are the additive extension point. |
| width, order or meaning of an existing field changes | MAJOR | requires a **new magic**, not a version bump |
| golden vectors | — | append-only, never edited in place. A changed byte in an existing vector means the contract was **broken**, not updated. |

---

## 8. Freeze evidence

Runner: `bin/simple_seed test <absolute path to spec>`.

| Run | State | Result |
|---|---|---|
| 1 | as frozen | `Results: 81 total, 81 passed, 0 failed` |
| 2 | symmetric encoder+decoder swap of `host_memory_budget` / `device_memory_budget` | `Results: 81 total, 80 passed, 1 failed` |
| 3 | reverted | `Results: 81 total, 81 passed, 0 failed` |

Run 2 is the non-vacuity proof. The injected defect is **symmetric**, so every
round-trip assertion stayed green; the single failure was the exact-byte golden
assertion, which reported

```
expected ...0000004000000000 0000008000000000 ...
got      ...0000008000000000 0000004000000000 ...
```

This is the fourth independent confirmation that round-trip testing alone
cannot freeze a wire format.

Regression: the frozen receipt lane
(`test/01_unit/common/structural/receipt_contract_spec.spl`) stays
`Results: 64 total, 64 passed, 0 failed` — this group imports it and does not
disturb it.

---

## 9. Open items reported for ratification

1. **`CapabilitySet` (§12.6)** — never enumerated by the architecture, and the
   name is already a kernel type. Owned by the Clang lane. Not guessed.
2. **`ExecutionProfile` name duplication** — `contracts.spl`'s cost record and
   §21's policy record are two different things sharing one name. This group
   left the former alone and named the latter `StageExecutionProfile`. A
   ratification could rename the cost record to `ExecutionCostProfile` and free
   the name, but that edits ~20 call sites and belongs to a dedicated change.
3. **`offload_profile.spl` calls its `execution: ExecutionProfile` field
   "budgets/devices from the EXEC owner"** — but the struct it points at has no
   budget or device field at all. It should be re-pointed at
   `StageExecutionProfile`. Not done here: that file is the compiler lane's.
4. **`deterministic` vs `VerificationPolicy.Off`** — a profile can request
   determinism while asking for no verification, so the claim is unchecked.
   The architecture does not say these interact, so no invariant was invented.
   Worth ratifying whether `deterministic` should imply at least
   `DeterministicHash`.
5. **`execution/__init__.spl` was NOT edited.** It re-exports `contracts.*`
   only; the new modules are reached by their full path, exactly as the receipt
   spec reaches `receipt_types`. Adding the re-export is a one-line additive
   change if the lane wants package-level visibility.
