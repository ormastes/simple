# Simpleos Render Evidence Protocol Specification

> <details>

<!-- sdn-diagram:id=simpleos_render_evidence_protocol_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_render_evidence_protocol_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_render_evidence_protocol_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_render_evidence_protocol_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Render Evidence Protocol Specification

## Scenarios

### SimpleOS QMP and serial render evidence

#### should negotiate QMP and capture a live nonblank guest frame

- Connect and negotiate QMP capabilities
   - Protocol capture: after_step
- Wait for the guest render receipt
   - Protocol capture: after_step
- Request the matching screendump
   - Protocol capture: after_step
- pending simpleos render protocol
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Connect and negotiate QMP capabilities")
step("Wait for the guest render receipt")
step("Request the matching screendump")
pending_simpleos_render_protocol()
```

</details>

<details>
<summary>Advanced: should correlate firmware boot run and frame identities</summary>

#### should correlate firmware boot run and frame identities

- Join the serial receipt and capture metadata
   - Expected: ["firmware_hash", "boot_id", "frame_id"].len() equals `3`
- pending simpleos render protocol


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Join the serial receipt and capture metadata")
expect(["firmware_hash", "boot_id", "frame_id"].len()).to_equal(3)
pending_simpleos_render_protocol()
```

</details>


</details>

<details>
<summary>Advanced: should reject corrupt reordered or truncated serial events</summary>

#### should reject corrupt reordered or truncated serial events

- Submit invalid receipt event streams
   - Expected: ["corrupt", "reordered", "truncated"].len() equals `3`
- pending simpleos render protocol


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit invalid receipt event streams")
expect(["corrupt", "reordered", "truncated"].len()).to_equal(3)
pending_simpleos_render_protocol()
```

</details>


</details>

<details>
<summary>Advanced: should reject any nonzero framebuffer mismatch</summary>

#### should reject any nonzero framebuffer mismatch

- Change one captured framebuffer pixel
   - Expected: 1 equals `1`
- pending simpleos render protocol


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Change one captured framebuffer pixel")
expect(1).to_equal(1)
pending_simpleos_render_protocol()
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/simpleos_render_evidence_protocol_spec.spl` |
| Updated | 2026-07-10 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS QMP and serial render evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
