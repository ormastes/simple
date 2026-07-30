# SimpleOS QEMU WM Real-Screen Test Plan

Updated: 2026-07-30

## Purpose

Prove that SimpleOS boots in QEMU, renders the canonical desktop through the
real WM/Draw IR/Engine2D path, presents a real screen, and applies ordered
pointer, keyboard, and focus events to subsequently captured frames. This plan
covers x86_64 compatibility evidence and the production AArch64/HVF path on
macOS. SIMD validation is a prerequisite, not a substitute for a guest render.

The broader host Vulkan and Metal work remains separate. A host backend PASS
must not be used as QEMU evidence, and a QEMU failure must not invalidate
already accepted host evidence.

## Single-Session Ownership

Exactly one agent session owns QEMU execution for this plan. That session owns:

- QEMU process and port discovery;
- guest image/kernel selection and construction;
- SIMD prerequisite execution;
- QEMU launch, QMP input injection, capture, shutdown, and cleanup;
- evidence correlation and the final PASS/FAIL report.

No root session or sidecar may launch another QEMU instance while the owner is
active. Other agents may review source or reports, but may not run QEMU,
reserve its ports, alter its evidence directory, or rebuild its guest
artifacts. If the owner stops, ownership must be explicitly transferred before
another session launches QEMU.

Only one bounded run is allowed per architecture after its prerequisites pass.
There is no automatic retry. A failed live run is preserved and reviewed
before another run is authorized.

## 2026-07-30 Sole-Owner Preflight

The sole QEMU agent ran:

```sh
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --preflight
```

Worktree revision:
`3295304499cfecc7fdbd1ea12d1b61871362869b`.

Result: `BLOCKED` (exit 1); no new VM was launched.

| Target | Result | Evidence |
|---|---|---|
| macOS AArch64 | READY transport only | HVF plus file-backed RAM tail is available |
| x86_64 TCG | BLOCKED | only `virtio-serial-unimplemented` transport is available |
| RISC-V TCG | BLOCKED | only `virtio-serial-unimplemented` transport is available |

Missing canonical artifacts:

- `build/os/simpleos_x86_64_host_gpu_probe.elf`
- `build/os/simpleos_arm64_host_gpu_probe.elf`
- `build/os/simpleos_arm64_desktop_engine2d.elf`
- the AArch64 desktop build manifest
- `fat32-arm64-desktop.img`
- `simpleos_desktop_gui_x86_64.elf`

A pre-existing x86 QEMU run ended before this preflight completed. Its retained
serial evidence is:

```text
/private/tmp/simple-qemu-live-20260730/build/qemu-live/evidence/serial-vfsfix.log
```

That run is a FAIL, not reusable evidence: vector-font registration accepted
zero faces, host-GPU fell back to software, and execution ended with
`runtime error: field access on nil receiver`. Its `frame-v2.png` and
`frame-v2.ppm` captures are diagnostic only because there is no accepted
ordered-event receipt.

At preflight time the host Stage 3 compiler build was CPU-active and free disk
was approximately 8.9 GiB. Launching another VM then would have competed with
that build. QEMU execution is therefore postponed to the sole QEMU owner until
the host build exits and the artifact prerequisites below are satisfied.

## Current Execution Order

The sole QEMU owner must start from current `origin/main`, record the exact
revision, confirm no other QEMU process owns the selected ports, and use a
clean isolated worktree and distinct build/evidence directories.

1. Confirm adequate disk and that no host bootstrap/native build writes the
   intended guest cache.
2. Run the SIMD prerequisite once:

   ```sh
   sh scripts/check/check-simpleos-qemu-engine2d-simd-kernels.shs
   ```

3. Materialize the required x86_64 and AArch64 guest artifacts without a full
   bootstrap. Build AArch64 desktop evidence through:

   ```sh
   sh scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs
   ```

4. Re-run the aggregate preflight once:

   ```sh
   sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --preflight
   ```

   Do not launch QEMU unless the selected row and all required artifact
   identities are READY.

5. Run the x86_64 ordered render/event compatibility wrapper once when its
   transport and guest ELF are ready:

   ```sh
   sh scripts/check/check-simpleos-x86-64-wm-render-event-evidence.shs
   ```

6. Run the aggregate host-GPU/Draw IR evidence wrapper once:

   ```sh
   sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs
   ```

7. Run the production AArch64 ordered-event evidence once:

   ```sh
   sh scripts/check/check-simpleos-arm64-qmp-input-evidence.shs
   ```

8. Preserve all serial, QMP, argv, manifest, capture, checksum, timing, and
   process-cleanup evidence. Stop after the first real failure; do not retry or
   replace a failed backend with software.

## Acceptance Gates

A target passes only when one correlated run proves all of the following:

- the selected backend and guest transport are real and fail closed;
- the captured screen is produced by the canonical WM -> Draw IR -> Engine2D
  guest path, not by a synthetic image or CPU/software fallback;
- a positive initial frame ID, checksum, dimensions, and presentation receipt
  agree across guest serial, host/QEMU evidence, and capture;
- the ordered event sequence is exactly
  `focus,pointer_move,pointer_down,pointer_up,key_down,key_up`;
- each accepted semantic action advances the expected state/frame generation;
- before/after captures differ at the expected semantic region;
- vector-font identity and glyph material are accepted rather than silently
  replaced with a bitmap fallback;
- SIMD prerequisites pass for the guest architecture, while the live render
  independently proves the pixels;
- QEMU argv, accelerator, guest artifact hashes, revision, timing, maximum RSS,
  and clean shutdown are retained;
- no orphan QEMU process or reserved port remains.

`BLOCKED`, `unsupported`, compile-only output, source inspection, screenshots
without receipts, software fallback, and historical captures do not satisfy
this plan.

## Immediate Remaining Work

1. Let the active host compiler build release CPU and disk pressure.
2. Have the sole QEMU owner construct and attest the missing AArch64 artifacts
   incrementally.
3. Fix or formally retain the x86_64/RISC-V VirtIO-serial transport blocker;
   do not claim those rows from AArch64 evidence.
4. Diagnose the retained x86 nil-receiver failure and vector-font rejection
   before authorizing its next bounded live run.
5. Execute the AArch64/HVF render-and-event run and publish its correlated
   evidence.

Merge owner and final reviewer: root/high-capability Codex agent. QEMU launch
owner: one explicitly assigned QEMU agent session only.
