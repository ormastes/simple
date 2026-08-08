<!-- codex-design -->
# GPU MMU Detail Design

<!-- sdn-diagram:id=gpu_mmu.design -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_mmu.design hash=sha256:auto render=ascii
@layout dag
@direction LR

Request -> Plan
Plan -> AcquireLease
AcquireLease -> StageOrDirect
StageOrDirect -> ResidentView
ResidentView -> ReleaseLease
StageOrDirect -> Journal
Journal -> Checkpoint
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_mmu.design hash=sha256:auto
Request -> Plan -> AcquireLease -> StageOrDirect -> ResidentView -> ReleaseLease
                                      |
                                      +-> Journal -> Checkpoint
```

</details>
<!-- sdn-diagram:end -->

## Data

- `ObjectRef`: compact descriptor slot plus generation.
- `EntityRef`: exactly 64 bits: object slot plus compact local index.
- `ResidentView<T>`: device address, byte length, object slot, and lease epoch; validity also depends on the descriptor generation captured by its lease.
- Descriptor: residency tier, size, generation, lease epoch, pin/in-flight counts, artifact ID, dirty flag, and last/next-use metadata. One descriptor represents an arena/shard.
- `ArtifactId`: canonical SHA-256 text binding immutable bytes and schema/version metadata.
- `StageReceipt`: backend/mode, input/output identities, byte counts, elapsed/cost fields, and deterministic result identity.

## Object VM

Allocation reuses free slots only after incrementing generation. Lease acquisition validates the handle and current residency, increments protection state, and returns a view snapshot. Every view operation checks slot, generation, and lease epoch. Release invalidates that epoch. Eviction first checks pins and in-flight transfers.

## Store and Recovery

Write bytes to their content path, verify the computed ID, then append a complete journal record and publish a checkpoint/manifest root. Recovery scans only complete records, validates referenced immutable blobs, and returns a typed corruption/partial-tail result. Duplicate content reuses its existing blob.

## Planner

Normalize and stably sort requests. Compute reload/recompute cost and a fixed-point retain score from reuse probability, minimum replacement cost, and bytes. Preserve affinity groups where budgets allow; pinned/in-flight reservations are mandatory. Produce deterministic reservations, transfers, evictions, prefetches, lease intents, estimated cost, and receipt seed. Fixed workload calibration compares predicted and observed cost using integer bounds.

## Backends

- Staged: chunk through a reusable ring capped by staging budget, emitting one receipt for the completed object.
- Direct: probe first; unsupported returns explicit capability failure. Available runs must match staged output bytes.
- Device initiated: requires the independent experimental flag and capability; otherwise returns gated/unsupported without mutation.

## Errors and Observability

Errors distinguish stale handle, stale lease, protected eviction, budget exceeded, unsupported capability, corrupt artifact, partial journal, and calibration miss. Counters cover live descriptors, leases, coalesced misses, staged high-water bytes, transfers, evictions, recovery rejects, predicted cost, and observed cost.

## Verification

Focused unit specs own branch/error behavior. The system scenario in `doc/03_plan/sys_test/gpu_mmu.md` proves cross-module flows and produces the mirrored operator manual. No GUI/TUI design is applicable.
