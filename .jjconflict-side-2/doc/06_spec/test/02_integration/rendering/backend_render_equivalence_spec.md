# Backend Render Equivalence

> Proves that semantic agreement is accepted only when independent producers,

<!-- sdn-diagram:id=backend_render_equivalence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_render_equivalence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_render_equivalence_spec -> std
backend_render_equivalence_spec -> common
backend_render_equivalence_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_render_equivalence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Render Equivalence

Proves that semantic agreement is accepted only when independent producers,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/backend_render_equivalence_spec.spl` |
| Updated | 2026-07-10 |
| Generator | `simple spipe-docgen` (Simple) |

Proves that semantic agreement is accepted only when independent producers,
real completion, positive handles, and exact absolute pixels all agree.

## Scenarios

### Backend render equivalence

#### should accept independent completed records with exact oracle pixels

- Capture independent backend render records
   - Protocol capture: after_step
- Validate provenance and frame completion
   - Protocol capture: after_step
- Compare detailed backend state
   - Protocol capture: after_step
- Compare readback against the absolute oracle
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: result.reason equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture independent backend render records")
val left = backend_render_fixture("engine2d-owner", "vulkan", "vulkan", "vulkan", "native", "none", 42, "device_readback", BACKEND_RENDER_FIXTURE_HASH, 12)
val right = backend_render_fixture("renderdoc-capture", "directx", "vulkan", "vulkan", "translated", "simple-directx-on-vulkan", 73, "device_readback", BACKEND_RENDER_FIXTURE_HASH, 12)
step("Validate provenance and frame completion")
step("Compare detailed backend state")
step("Compare readback against the absolute oracle")
val result = verify_backend_render_equivalence(left, right, BackendRenderOracle(oracle_mismatch_count: 0, pair_mismatch_count: 0, blur_or_tolerance: false))
expect(result.passed).to_be(true)
expect(result.reason).to_equal("pass")
```

</details>

<details>
<summary>Advanced: should reject two records from the same producer</summary>

#### should reject two records from the same producer

- Reuse one producer identity for both records
   - Expected: result.reason equals `non-independent-producers`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reuse one producer identity for both records")
val left = backend_render_fixture("same", "vulkan", "vulkan", "vulkan", "native", "none", 42, "device_readback", BACKEND_RENDER_FIXTURE_HASH, 12)
val right = backend_render_fixture("same", "vulkan", "vulkan", "vulkan", "native", "none", 73, "device_readback", BACKEND_RENDER_FIXTURE_HASH, 12)
val result = verify_backend_render_equivalence(left, right, BackendRenderOracle(oracle_mismatch_count: 0, pair_mismatch_count: 0, blur_or_tolerance: false))
expect(result.reason).to_equal("non-independent-producers")
```

</details>


</details>

<details>
<summary>Advanced: should reject incomplete frames and zero backend handles</summary>

#### should reject incomplete frames and zero backend handles

- Submit incomplete and synthetic-handle records
   - Expected: result.reason equals `right-invalid-handle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit incomplete and synthetic-handle records")
val left = backend_render_fixture("left", "vulkan", "vulkan", "vulkan", "native", "none", 42, "device_readback", BACKEND_RENDER_FIXTURE_HASH, 12)
val right = backend_render_fixture("right", "vulkan", "vulkan", "vulkan", "native", "none", 0, "device_readback", BACKEND_RENDER_FIXTURE_HASH, 12)
val result = verify_backend_render_equivalence(left, right, BackendRenderOracle(oracle_mismatch_count: 0, pair_mismatch_count: 0, blur_or_tolerance: false))
expect(result.reason).to_equal("right-invalid-handle")
```

</details>


</details>

<details>
<summary>Advanced: should reject one changed pixel without blur or tolerance</summary>

#### should reject one changed pixel without blur or tolerance

- Change exactly one readback pixel
- Report the exact mismatch
   - Expected: result.reason equals `oracle-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Change exactly one readback pixel")
val left = backend_render_fixture("left", "vulkan", "vulkan", "vulkan", "native", "none", 42, "device_readback", BACKEND_RENDER_FIXTURE_HASH, 12)
val right = backend_render_fixture("right", "vulkan", "vulkan", "vulkan", "native", "none", 73, "device_readback", BACKEND_RENDER_FIXTURE_HASH, 12)
step("Report the exact mismatch")
val result = verify_backend_render_equivalence(left, right, BackendRenderOracle(oracle_mismatch_count: 1, pair_mismatch_count: 1, blur_or_tolerance: false))
expect(result.reason).to_equal("oracle-mismatch")
```

</details>


</details>

<details>
<summary>Advanced: should reject host-array pixels labeled as device readback</summary>

#### should reject host-array pixels labeled as device readback

- Submit DirectX emulation host pixels with device provenance
   - Expected: result.reason equals `left-contradictory-provenance`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit DirectX emulation host pixels with device provenance")
val left = backend_render_fixture("left", "software", "software", "cpu", "software", "none", 42, "device_readback", BACKEND_RENDER_FIXTURE_HASH, 12)
val right = backend_render_fixture("right", "vulkan", "vulkan", "vulkan", "native", "none", 73, "device_readback", BACKEND_RENDER_FIXTURE_HASH, 12)
val result = verify_backend_render_equivalence(left, right, BackendRenderOracle(oracle_mismatch_count: 0, pair_mismatch_count: 0, blur_or_tolerance: false))
expect(result.reason).to_equal("left-contradictory-provenance")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
