# Driver frontend-offload decision (pure twin)

> `driver_frontend_offload_receipt_for(env, fallback)` is the env-free twin of

<!-- sdn-diagram:id=frontend_offload_driver_unit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=frontend_offload_driver_unit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

frontend_offload_driver_unit_spec -> std
frontend_offload_driver_unit_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=frontend_offload_driver_unit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver frontend-offload decision (pure twin)

`driver_frontend_offload_receipt_for(env, fallback)` is the env-free twin of

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / Driver |
| Status | Implemented |
| Source | `/home/yoon/dev/simple-gpu-frontend/test/01_unit/compiler/driver/frontend_offload_driver_unit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

`driver_frontend_offload_receipt_for(env, fallback)` is the env-free twin of
`driver_frontend_offload_decision()`: same resolver, same `gpu_parse_available =
false` (Wave 0), same receipt text the driver traces. Pinning it here proves the
driver wiring without a deployed pure-Simple binary.

## Scenarios

### driver frontend offload decision

#### records the offload decision receipt for the default switch

- Record the offload decision receipt
   - Expected: demoted.is_ok() is true
   - Expected: frontend_offload_parse_mode_text(demoted.unwrap()) equals `cpu_reference`
   - Expected: demoted.unwrap().fallback_reason equals `parse_mode_unimplemented`
   - Expected: refused.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Record the offload decision receipt")
env_set("SIMPLE_FRONTEND_OFFLOAD", "on")
env_set("SIMPLE_FRONTEND_OFFLOAD_FALLBACK", "allow-cpu")
val demoted = driver_frontend_offload_decision()
env_set("SIMPLE_FRONTEND_OFFLOAD_FALLBACK", "require-requested")
val refused = driver_frontend_offload_decision()
env_set("SIMPLE_FRONTEND_OFFLOAD", "")
env_set("SIMPLE_FRONTEND_OFFLOAD_FALLBACK", "")
expect(demoted.is_ok()).to_equal(true)
expect(frontend_offload_parse_mode_text(demoted.unwrap())).to_equal("cpu_reference")
expect(demoted.unwrap().fallback_reason).to_equal("parse_mode_unimplemented")
expect(refused.is_err()).to_equal(true)
expect(refused.unwrap_err()).to_contain("frontend_offload_required_mode_unavailable")
```

</details>

#### defaults to CPU reference when nothing is set

- Default to CPU reference when nothing is set
   - Expected: receipt.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Default to CPU reference when nothing is set")
val receipt = driver_frontend_offload_receipt_for("", "")
expect(receipt.is_ok()).to_equal(true)
expect(receipt.unwrap()).to_equal(
    "[frontend-offload] requested=cpu_reference selected=cpu_reference reason= source=default")
```

</details>

#### demotes auto with the auto-profile reason

- Demote honestly when GPU parsing is unimplemented
   - Expected: receipt.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Demote honestly when GPU parsing is unimplemented")
val receipt = driver_frontend_offload_receipt_for("auto", "")
expect(receipt.is_ok()).to_equal(true)
expect(receipt.unwrap()).to_equal(
    "[frontend-offload] requested=cpu_reference selected=cpu_reference reason=auto_profile_not_implemented_wave_1 source=env")
```

</details>

#### demotes honestly when GPU parsing is unimplemented

- Demote honestly when GPU parsing is unimplemented
   - Expected: receipt.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Demote honestly when GPU parsing is unimplemented")
val receipt = driver_frontend_offload_receipt_for("on", "allow-cpu")
expect(receipt.is_ok()).to_equal(true)
expect(receipt.unwrap()).to_equal(
    "[frontend-offload] requested=hybrid_vector_gpu selected=cpu_reference reason=parse_mode_unimplemented source=env")
```

</details>

#### refuses to demote under require-requested

- Refuse to demote under require-requested
   - Expected: receipt.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Refuse to demote under require-requested")
val receipt = driver_frontend_offload_receipt_for("on", "require-requested")
expect(receipt.is_err()).to_equal(true)
expect(receipt.unwrap_err()).to_contain("frontend_offload_required_mode_unavailable")
```

</details>

#### rejects unknown switch text instead of silently selecting off

- Resolve the frontend offload switch from CLI, env, and config
   - Expected: receipt.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve the frontend offload switch from CLI, env, and config")
val receipt = driver_frontend_offload_receipt_for("bogus", "")
expect(receipt.is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

## Generation history

Generated by `simple spipe-docgen` (Simple).
Source SHA-256: `834f88fc6ad787d1ee7bebe89dd393152c24a0abe6dd28f4c0ff3d23f4774451`
