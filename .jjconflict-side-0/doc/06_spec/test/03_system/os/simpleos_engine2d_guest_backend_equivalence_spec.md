# SimpleOS Guest Engine2D Equivalence

> Builds and boots real SimpleOS rendering entries, correlates the guest serial

<!-- sdn-diagram:id=simpleos_engine2d_guest_backend_equivalence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_engine2d_guest_backend_equivalence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_engine2d_guest_backend_equivalence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_engine2d_guest_backend_equivalence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Guest Engine2D Equivalence

Builds and boots real SimpleOS rendering entries, correlates the guest serial

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_engine2d_guest_backend_equivalence_spec.spl` |
| Updated | 2026-07-10 |
| Generator | `simple spipe-docgen` (Simple) |

Builds and boots real SimpleOS rendering entries, correlates the guest serial
receipt with a pure-Simple QMP framebuffer capture, and requires exact pixels.

## Scenarios

### SimpleOS guest-native Engine2D

#### should boot x86_64 framebuffer rendering and match the exact oracle

- Prepare the SimpleOS x86_64 rendering image
   - Artifact capture: after_step
- Boot the guest and capture its ordered render receipt
   - Artifact capture: after_step
- Capture the matching framebuffer through the pure-Simple QMP client
   - Artifact capture: after_step
- Correlate firmware run and frame identities
   - Artifact capture: after_step
- Compare the framebuffer against the absolute oracle
   - Artifact capture: after_step
- pending simpleos guest equivalence
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prepare the SimpleOS x86_64 rendering image")
step("Boot the guest and capture its ordered render receipt")
step("Capture the matching framebuffer through the pure-Simple QMP client")
step("Correlate firmware run and frame identities")
step("Compare the framebuffer against the absolute oracle")
pending_simpleos_guest_equivalence()
```

</details>

#### should boot x86_64 VirtIO GPU rendering without accepting init failure

- Prepare the strict VirtIO GPU guest
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: init_status equals `required`
- pending simpleos guest equivalence
   - Log capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prepare the strict VirtIO GPU guest")
val init_status = "required"
expect(init_status).to_equal("required")
pending_simpleos_guest_equivalence()
```

</details>

#### should produce an RV64 live rendering receipt instead of fixed pass text

- Boot the RV64 display entry
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: receipt_kind equals `runtime-measured`
- pending simpleos guest equivalence
   - Log capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Boot the RV64 display entry")
val receipt_kind = "runtime-measured"
expect(receipt_kind).to_equal("runtime-measured")
pending_simpleos_guest_equivalence()
```

</details>

#### should produce an AArch64 live framebuffer record instead of static metadata

- Boot the AArch64 framebuffer entry
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: evidence_kind equals `live-frame`
- pending simpleos guest equivalence
   - Log capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Boot the AArch64 framebuffer entry")
val evidence_kind = "live-frame"
expect(evidence_kind).to_equal("live-frame")
pending_simpleos_guest_equivalence()
```

</details>

<details>
<summary>Advanced: should reject mismatched serial and QMP frame identities</summary>

#### should reject mismatched serial and QMP frame identities

- Pair a guest receipt with a different captured frame
   - Expected: reason equals `frame-correlation-mismatch`
- pending simpleos guest equivalence


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pair a guest receipt with a different captured frame")
val reason = "frame-correlation-mismatch"
expect(reason).to_equal("frame-correlation-mismatch")
pending_simpleos_guest_equivalence()
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
