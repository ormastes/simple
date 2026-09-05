# SimpleOS QEMU Input and Audio Specification

> SimpleOS receives ordered input and transfers application PCM through
> pure-Simple QEMU drivers.

This manual documents the executable SPipe scenarios in
`test/03_system/os/qemu/simpleos_io_audio_spec.spl`. A passing source check or
self-test is not live QEMU evidence. The `--live` scenario admits only retained
evidence rows supplied under `build/verify/simpleos-io-audio`; it does not
itself launch the four QEMU rows.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

## SimpleOS QEMU input and audio

### Prepare admitted guest artifacts and virtual devices

1. Boot the guest with the selected virtual devices.
2. Run `scripts/check/check-simpleos-io-audio-qemu.shs --preflight`.
3. Require exit code `0`, empty stderr, and
   `simpleos_io_audio_qemu_preflight=pass`.

This preflight checks QEMU device availability and required source owners. It
does not boot a guest or prove playback.

<details>
<summary>Executable SSpec</summary>

```simple
# @req REQ-SSPEC-SYSTEM
step("prepares admitted guest artifacts and virtual devices")
step("Boot the guest with the selected virtual devices")
val (out, err, code) = run_io_audio_qemu_check("--preflight")
expect(code).to_equal(0)
expect(err).to_equal("")
expect(out).to_contain("simpleos_io_audio_qemu_preflight=pass")
```

</details>

### Deliver guest input and non-silent playback and capture

1. Open the event and audio endpoints and run the canonical checker with
   `--live`.
2. Inject keyboard, pointer, and controller events; require the x86_64
   VirtIO-sound row.
3. Render the deterministic audio scene and require the aggregate PASS marker.
4. Retain platform evidence and resource receipts; require the x86_64 HDA row.
5. Require the AArch64 and RISC-V VirtIO-sound rows.

For AArch64 and RISC-V VirtIO-sound rows, the checker also requires a fresh
host-created PCM16 stereo 48 kHz WAV and a provenance record bound to the WAV,
guest kernel, source set, and QEMU identity. WAV proves playback only; capture
remains a separate guest/device receipt.

<details>
<summary>Executable SSpec</summary>

```simple
step("Open the event and audio endpoints")
val (out, err, code) = run_io_audio_qemu_check("--live")
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

### Validate host-observed WAV playback without claiming capture

1. Create valid and rejected host WAV evidence fixtures.
2. Require admission of non-silent PCM16 stereo 48 kHz playback.
3. Reject silent, truncated, symlinked, and stale WAV files.
4. Require `capture_claim=none`.

<details>
<summary>Executable SSpec</summary>

```simple
step("Create valid and rejected host WAV evidence fixtures")
val (out, err, code) = run_virtio_snd_wav_self_test()
expect(code).to_equal(0)
expect(err).to_equal("")
expect(out).to_contain("simpleos_virtio_snd_qemu_wav_self_test=pass")
expect(out).to_contain("cases=valid,silent,truncated,symlink,stale")
expect(out).to_contain("capture_claim=none")
```

</details>

### Reject host substitutes, stale artifacts, and incomplete receipts

1. Validate guest and pure-Simple provenance with `--self-test`.
2. Require exit code `0`, empty stderr, and
   `simpleos_io_audio_qemu_self_test=pass`.

The self-test uses generated fixture logs. It proves checker behavior only and
must never be reported as guest execution or host-observed audio.

<details>
<summary>Executable SSpec</summary>

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects host substitutes stale artifacts and incomplete receipts")
step("Validate guest and pure-Simple provenance")
val (out, err, code) = run_io_audio_qemu_check("--self-test")
expect(code).to_equal(0)
expect(err).to_equal("")
expect(out).to_contain("simpleos_io_audio_qemu_self_test=pass")
```

</details>

</details>

## Traceability and evidence boundary

- Requirements: `REQ-001`, `REQ-002`, `REQ-003`, `REQ-015`, `REQ-017`,
  `REQ-018`.
- Executable source:
  `test/03_system/os/qemu/simpleos_io_audio_spec.spl`.
- Checker: `scripts/check/check-simpleos-io-audio-qemu.shs`.
- Live VirtIO runner: `scripts/check/check-simpleos-virtio-snd-qemu.shs`.
- Host-WAV evidence design:
  `doc/03_plan/sys_test/simpleos_io_audio_host_wav_evidence.md`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware and OS |
| Status | Active; AArch64/RISC-V host-WAV playback implemented |
| Source | `test/03_system/os/qemu/simpleos_io_audio_spec.spl` |
| Generator | SPipe-compatible manual mirror |
