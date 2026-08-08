# SimpleOS QEMU input and audio

> This operator-facing system check proves that prepared SimpleOS QEMU guests

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS QEMU input and audio

This operator-facing system check proves that prepared SimpleOS QEMU guests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Requirements | doc/02_requirements/feature/simpleos_qemu_host_gpu_2d.md and doc/02_requirements/nfr/simpleos_qemu_host_gpu_2d.md |
| Plan | doc/03_plan/sys_test/simpleos_qemu_host_gpu_2d.md |
| Design | doc/05_design/simpleos_qemu_host_gpu_2d.md |
| Research | doc/01_research/local/simpleos_qemu_host_gpu_2d.md and doc/01_research/domain/simpleos_qemu_host_gpu_2d.md |
| Source | `test/03_system/os/qemu/simpleos_io_audio_spec.spl` |
| Updated | 2026-08-08 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

This operator-facing system check proves that prepared SimpleOS QEMU guests
receive ordered VirtIO input and complete non-silent PCM playback and capture
through pure-Simple guest drivers. It is for SimpleOS driver, compositor, and
release maintainers validating x86_64, AArch64, and RISC-V environments.

## Scope and Preconditions

The canonical checker owns guest artifact admission, QEMU device arguments,
boot, event injection, and audio receipt validation. A deployed source-matched
pure-Simple compiler and the QEMU binaries/devices named by the selected
environment profile must be available. Host substitutes and Rust bootstrap
seed artifacts are rejected.

**Requirements:** doc/02_requirements/feature/simpleos_qemu_host_gpu_2d.md and doc/02_requirements/nfr/simpleos_qemu_host_gpu_2d.md
**Plan:** doc/03_plan/sys_test/simpleos_qemu_host_gpu_2d.md
**Architecture:** doc/04_architecture/simpleos_qemu_host_gpu_2d.md
**Design:** doc/05_design/simpleos_qemu_host_gpu_2d.md
**Research:** doc/01_research/local/simpleos_qemu_host_gpu_2d.md and doc/01_research/domain/simpleos_qemu_host_gpu_2d.md

## Primary Workflow and Evidence

Run preflight first, then the live checker. Preflight may produce only typed
`Ready` admission: it never proves guest execution. Live evidence requires the
guest receipt rows for x86_64 VirtIO-snd and HDA plus AArch64 and RISC-V
VirtIO-snd. The self-test proves stale, host-substitute, and incomplete
receipts fail closed.

## Recovery and Troubleshooting

If preflight is blocked, use its stable reason to install the missing QEMU
binary/device or deploy the admitted pure-Simple guest artifact. A live failure
must be diagnosed from the retained serial log and checker reason; do not
downgrade to readiness or a host-generated receipt.

## Compatibility and Limitations

This spec proves the input/audio slice. It does not promote Vulkan rendering;
the separate Draw IR/Vulkan gate must provide live device execution and
device-origin readback before the combined environment can pass.

## Scenarios

### SimpleOS QEMU input and audio

#### delivers guest input and non-silent playback and capture

- Boot the guest with the selected virtual devices
   - Log capture: after_step
   - Evidence: log output verified by 4 expected checks
   - Expected: code equals `CHECK_SUCCESS`
   - Expected: err equals ``
   - Expected: admission.status equals `UiEnvironmentAdmissionStatus.Ready`
   - Expected: admission.reason equals `live-guest-proof-required`
- Open the event and audio endpoints
   - Log capture: after_step
   - Evidence: log output verified by 3 expected checks
   - Expected: profile.required_evidence equals `UiEnvironmentEvidenceClass.LiveGuest`
   - Expected: code equals `CHECK_SUCCESS`
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

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Boot the guest with the selected virtual devices")
val (out, err, code) = run_io_audio_qemu_check("--preflight")
# oracle: the canonical checker uses process success only after all prerequisites pass.
expect(code).to_equal(CHECK_SUCCESS)
expect(err).to_equal("")
expect(out).to_contain("simpleos_io_audio_qemu_preflight=pass")
val profile = simpleos_qemu_2d_environment_profiles()[X86_PROFILE_INDEX]
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
val profile = simpleos_qemu_2d_environment_profiles()[X86_PROFILE_INDEX]
expect(profile.required_evidence).to_equal(UiEnvironmentEvidenceClass.LiveGuest)
expect(code).to_equal(CHECK_SUCCESS)
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
   - Log capture: after_step
   - Evidence: log output verified by 2 expected checks
   - Expected: code equals `CHECK_SUCCESS`
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate guest and pure-Simple provenance")
val (out, err, code) = run_io_audio_qemu_check("--self-test")
expect(code).to_equal(CHECK_SUCCESS)
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


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simpleos_qemu_host_gpu_2d.md and doc/02_requirements/nfr/simpleos_qemu_host_gpu_2d.md`
- **Plan:** `doc/03_plan/sys_test/simpleos_qemu_host_gpu_2d.md`
- **Design:** `doc/05_design/simpleos_qemu_host_gpu_2d.md`
- **Research:** `doc/01_research/local/simpleos_qemu_host_gpu_2d.md and doc/01_research/domain/simpleos_qemu_host_gpu_2d.md`


</details>
