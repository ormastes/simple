# simpleos_io_audio_spec

> SimpleOS receives ordered input and transfers application PCM through pure-Simple QEMU drivers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simpleos_io_audio_spec

SimpleOS receives ordered input and transfers application PCM through pure-Simple QEMU drivers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/simpleos_io_audio_spec.spl` |
| Updated | 2026-08-08 |
| Generator | `simple spipe-docgen` (Simple) |

SimpleOS receives ordered input and transfers application PCM through pure-Simple QEMU drivers.

## Scenarios

### SimpleOS QEMU input and audio

#### delivers guest input and non-silent playback and capture

- Boot the guest with the selected virtual devices
   - Log capture: after_step
   - Evidence: log output verified by 4 expected checks
   - Expected: code equals `0`
   - Expected: err equals ``
   - Expected: admission.status equals `UiEnvironmentAdmissionStatus.Ready`
   - Expected: admission.reason equals `live-guest-proof-required`
- Open the event and audio endpoints
   - Log capture: after_step
   - Evidence: log output verified by 3 expected checks
   - Expected: profile.required_evidence equals `UiEnvironmentEvidenceClass.LiveGuest`
   - Expected: code equals `0`
   - Expected: err equals ``
- Inject keyboard pointer and controller events
   - Log capture: after_step
- Render the deterministic audio scene
   - Log capture: after_step
- Retain platform evidence and resource receipts
   - Log capture: after_step
- Run ARM64 and RISC-V VirtIO sound rows
   - Log capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Boot the guest with the selected virtual devices")
val (out, err, code) = run_io_audio_qemu_check("--preflight")
expect(code).to_equal(0)
expect(err).to_equal("")
expect(out).to_contain("simpleos_io_audio_qemu_preflight=pass")
val profile = simpleos_qemu_2d_environment_profiles()[0]
val admission = validate_ui_environment_evidence(
    profile,
    ui_environment_evidence(
        profile.id,
        UiEnvironmentEvidenceClass.HostReadiness,
        configured: true,
        runtime_available: true,
        qemu_arguments_bound: true
    )
)
expect(admission.status).to_equal(UiEnvironmentAdmissionStatus.Ready)
expect(admission.reason).to_equal("live-guest-proof-required")
expect(admission.promotion_eligible).to_be(false)

step("Open the event and audio endpoints")
val (out, err, code) = run_io_audio_qemu_check("--live")
val profile = simpleos_qemu_2d_environment_profiles()[0]
expect(profile.required_evidence).to_equal(UiEnvironmentEvidenceClass.LiveGuest)
expect(code).to_equal(0)
expect(err).to_equal("")
step("Inject keyboard pointer and controller events")
expect(out).to_contain("simpleos_io_audio_qemu_row=pass arch=x86_64 backend=virtio-snd")
step("Render the deterministic audio scene")
expect(out).to_contain("simpleos_io_audio_qemu_status=pass")
step("Retain platform evidence and resource receipts")
expect(out).to_contain("simpleos_io_audio_qemu_row=pass arch=x86_64 backend=hda")
step("Run ARM64 and RISC-V VirtIO sound rows")
expect(out).to_contain("simpleos_io_audio_qemu_row=pass arch=aarch64 backend=virtio-snd")
expect(out).to_contain("simpleos_io_audio_qemu_row=pass arch=riscv64 backend=virtio-snd")
```

</details>

<details>
<summary>Advanced: rejects host substitutes stale artifacts and incomplete receipts</summary>

#### rejects host substitutes stale artifacts and incomplete receipts

- Validate guest and pure-Simple provenance
   - Expected: code equals `0`
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate guest and pure-Simple provenance")
val (out, err, code) = run_io_audio_qemu_check("--self-test")
expect(code).to_equal(0)
expect(err).to_equal("")
expect(out).to_contain("simpleos_io_audio_qemu_self_test=pass")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
