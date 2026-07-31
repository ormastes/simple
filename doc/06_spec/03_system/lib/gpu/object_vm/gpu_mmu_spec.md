# Gpu Mmu Specification

> Tests covering GPU MMU system contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Mmu Specification

## Scenarios

### GPU MMU system contract

#### should create arena handles and acquire a lease

- Create arena handles and acquire a lease
- artifact id
   - Expected: view.length equals `1024`
   - Expected: view.object_slot equals `object.object_slot`
   - Expected: view.lease_epoch equals `1`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create arena handles and acquire a lease")
val table = fixture_table()
val object = table.allocate(
    1024,
    ResidencyTier.DeviceLocal,
    PersistencePolicy.Checkpoint,
    artifact_id(digest: valid_artifact(), byte_len: 16)
)
val lease = table.acquire_lease(object)
match lease:
    case Result.Ok(view):
        expect(view.length).to_equal(1024)
        expect(view.object_slot).to_equal(object.object_slot)
        expect(view.lease_epoch).to_equal(1)
    case Result.Err(_):
        expect(false).to_equal(true)
```

</details>

#### should reject stale handles and protected eviction

- Reject stale handles and protected eviction
- artifact id
   - Expected: table.pin(object, 1) is true
   - Expected: table.release(object) is false
   - Expected: table.pin(object, -1) is true
   - Expected: stale equals `Result.Err(PlacementError.StaleHandle)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject stale handles and protected eviction")
val table = fixture_table()
val object = table.allocate(
    128,
    ResidencyTier.DeviceLocal,
    PersistencePolicy.Checkpoint,
    artifact_id(digest: valid_artifact(), byte_len: 16)
)
expect(table.release_lease(ResidentView(
    device_address: 0,
    length: 0,
    object_slot: object.object_slot,
    lease_epoch: 999
))).to_equal(false)
expect(table.pin(object, 1)).to_equal(true)
expect(table.release(object)).to_equal(false)
expect(table.pin(object, -1)).to_equal(true)
val stale = table.acquire_lease(object_ref(
    object_slot: object.object_slot,
    generation: object.generation + 1
))
expect(stale).to_equal(Result.Err(PlacementError.StaleHandle))
expect(descriptor_table_is_stale(object, object_ref(
    object_slot: object.object_slot,
    generation: object.generation + 1
))).to_equal(true)
```

</details>

#### should stage artifacts through bounded pinned transfer bytes

- Stage an artifact through the bounded pinned ring
   - Expected: receipt.bytes_transferred equals `256`
   - Expected: receipt.bytes_transferred <= 256 is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Stage an artifact through the bounded pinned ring")
val backend = StagedPlacementBackend.with_budget(256, 128)
val plan = staged_plan(test_budget())
val transfer = backend.prefetch(plan)
match transfer:
    case Result.Ok(receipt):
        expect(receipt.bytes_transferred).to_equal(256)
        expect(receipt.bytes_transferred <= 256).to_equal(true)
    case Result.Err(_):
        expect(false).to_equal(true)
```

</details>

#### should recover CAS roots after interrupted and corrupt writes

- Recover the CAS after interrupted or corrupt writes
- store write object bytes
- store write object bytes
   - Expected: checkpoint.ok is true
   - Expected: recovered.ok is true
   - Expected: missing_root.ok is false
   - Expected: missing_root.error equals `checkpoint-missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Recover the CAS after interrupted or corrupt writes")
val store = fixture_store()
val object_a = object_ref(object_slot: 1, generation: 1)
val object_b = object_ref(object_slot: 2, generation: 1)
store.write_object_bytes(object_a, [1, 2, 3], artifact_id(digest: valid_artifact(), byte_len: 3))
store.write_object_bytes(object_b, [4, 5, 6, 7], artifact_id(digest: valid_artifact(), byte_len: 3))
val checkpoint = store.checkpoint(ObjectSetView(objects: [object_a, object_b]))
expect(checkpoint.ok).to_equal(true)
val recovered = cas_store_recover(store, checkpoint.root)
expect(recovered.ok).to_equal(true)
val missing_root = cas_store_recover(store, artifact_id(digest: valid_artifact(), byte_len: 0))
expect(missing_root.ok).to_equal(false)
expect(missing_root.error).to_equal("checkpoint-missing")
```

</details>

#### should plan from liveness and cost with deterministic ordering

- Plan placement from liveness cost and budgets
   - Expected: primary.receipt_seed equals `replay.receipt_seed`
   - Expected: primary.estimated_cost.predicted_latency_us equals `replay.estimated_cost.predicted_latency_us`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan placement from liveness cost and budgets")
val primary = make_deterministic_plan(request_set(), test_budget())
val replay = make_deterministic_plan([request(3, 5), request(1, 20), request(2, 10)], test_budget())
expect(primary.receipt_seed).to_equal(replay.receipt_seed)
expect(primary.estimated_cost.predicted_latency_us).to_equal(replay.estimated_cost.predicted_latency_us)
```

</details>

#### should compare staged and direct backend bytes when available

- Compare staged and direct backend bytes
   - Expected: direct_value.bytes_transferred equals `staged_value.bytes_transferred`
   - Expected: false is true
   - Expected: false is true
   - Expected: false is true
   - Expected: err equals `PlacementError.Unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare staged and direct backend bytes")
val plan = staged_plan(test_budget())
val staged = StagedPlacementBackend.with_budget(1024, 2048)
val staged_receipt = staged.prefetch(plan)
val direct = DirectPlacementBackend()
val direct_available = env_get("SIMPLE_MMU_DIRECT_BACKEND") == "1"
if direct_available:
    val direct_receipt = direct.prefetch(plan)
    match staged_receipt:
        case Result.Ok(staged_value):
            match direct_receipt:
                case Result.Ok(direct_value):
                    expect(direct_value.bytes_transferred).to_equal(staged_value.bytes_transferred)
                case Result.Err(_):
                    expect(false).to_equal(true)
        case Result.Err(_):
            expect(false).to_equal(true)
else:
    match direct.prefetch(plan):
        case Result.Ok(_):
            expect(false).to_equal(true)
        case Result.Err(err):
            expect(err).to_equal(PlacementError.Unsupported)
```

</details>

#### should keep device-initiated path behind explicit gate

- Keep device-initiated placement behind its gate
- env get
   - Expected: false is true
   - Expected: err equals `PlacementError.Unsupported`
   - Expected: recovered.ok is false
   - Expected: recovered.recovered_objects equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep device-initiated placement behind its gate")
val device = DeviceInitiatedPlacementBackend()
expect(device.probe().available).to_equal(
    env_get("SIMPLE_MMU_DEVICE_INITIATED_BACKEND") == "1"
)
val plan = staged_plan(test_budget())
val acquired = device.acquire(plan)
match acquired:
    case Result.Ok(_):
        expect(false).to_equal(true)
    case Result.Err(err):
        expect(err).to_equal(PlacementError.Unsupported)
val recovered = device.recover(artifact_id(digest: valid_artifact(), byte_len: 1))
expect(recovered.ok).to_equal(false)
expect(recovered.recovered_objects).to_equal(0)
```

</details>

#### should hold host RSS within the fixed staging+queue+manifest bound

- Measure the fixed host RSS bound
   - Expected: fixed_ten equals `fixed_one`
   - Expected: fixed_one equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Measure the fixed host RSS bound")
val fixed_one = estimate_staged_peak(1)
val fixed_ten = estimate_staged_peak(10)
expect(fixed_ten).to_equal(fixed_one)
expect(fixed_one).to_equal(256)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/03_system/lib/gpu/object_vm/gpu_mmu_spec.spl` |
| Updated | 2026-07-31 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GPU MMU system contract.
- GPU MMU system contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
