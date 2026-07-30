# SimpleOS QEMU WM real-screen evidence plan

Updated: 2026-07-30

Status: **pending: the prior live run failed/inadmissible; the next manual
real-screen run awaits a current admitted artifact, exclusive ownership, and
manual user input.**

## Scope and ownership

This plan proves the canonical guest WM -> Draw IR -> Engine2D path, not a
host Vulkan/Metal result.  It covers x86_64 compatibility evidence and the
production AArch64/HVF path on macOS.  SIMD is a prerequisite, never a
substitute for a correlated guest render.

Exactly one delegated QEMU agent session owns each scoped execution: guest
artifact construction, QEMU process/port discovery, launch, captures,
evidence directory, shutdown, and failure report.  No sidecar may launch a
second VM, reserve its port, alter its run directory, or rebuild its artifact.
Ownership transfers explicitly before a different session launches QEMU.
Only one bounded live run per architecture is allowed after prerequisites;
there is no automatic retry.  Preserve and review a failure before authorizing
another run.

- The delegated QEMU agent owns build/launch/evidence for this lane.
- `/root` is merge owner; this lane does not commit or push.
- An independent high-capability reviewer must review the completed bundle,
  provenance, and fail-closed results before any PASS or promotion claim.

## Manual real-screen acceptance bar

| ID | Required proof |
|---|---|
| REQ-QRS-001 | Current integrated x86_64 WM reaches a guest WM-ready marker in a visible Cocoa QEMU window; retain clean source revision, ELF/EFI hashes, exact argv and PID. |
| REQ-QRS-002 | The same run records `requested=cpu_simd`, `actual=cpu_simd`, CPU profile/features, positive native-SIMD hits, and no fallback. |
| REQ-QRS-003 | Before/after QMP captures have dimensions, nonblank/bounds metrics, checksums and correlated generations; matching macOS QEMU-window captures are retained. |
| REQ-QRS-004 | A user physically clicks and serial proves ordered IRQ/target/handled/frame evidence. |
| REQ-QRS-005 | A user physically press/moves/releases a title bar; serial proves target, original/final coordinates, positive delta and changed frame. |
| REQ-QRS-006 | A user physically types `a`; serial proves down/up, committed text, focus target and later frame state. |
| REQ-QRS-007 | A user physically presses/releases Ctrl; serial proves distinct modifier down/up transitions. |
| REQ-QRS-008 | The interaction interval has ten or more guest frame intervals, p50/p95 render/present timing, QEMU host CPU samples and bounded heap delta. |

QMP `send-key`, QMP pointer injection, AppleScript input, headless capture,
source-only assertions, or an unsupported human assertion are never manual
acceptance evidence.  Automated wrappers and QMP input are useful diagnostic
or automated lanes only; their events may not be relabeled as physical Cocoa
input.  This plan does not claim that a physical action occurred.

## 2026-07-30 sole-owner preflight

The sole QEMU agent ran:

```sh
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --preflight
```

Worktree revision: `3295304499cfecc7fdbd1ea12d1b61871362869b`.
Result: `BLOCKED` (exit 1); no new VM was launched.

| Target | Result | Evidence |
|---|---|---|
| macOS AArch64 | READY transport only | HVF plus file-backed RAM tail available |
| x86_64 TCG | BLOCKED | only `virtio-serial-unimplemented` transport available |
| RISC-V TCG | BLOCKED | only `virtio-serial-unimplemented` transport available |

Missing canonical artifacts were:

- `build/os/simpleos_x86_64_host_gpu_probe.elf`
- `build/os/simpleos_arm64_host_gpu_probe.elf`
- `build/os/simpleos_arm64_desktop_engine2d.elf`
- AArch64 desktop build manifest and `fat32-arm64-desktop.img`
- `simpleos_desktop_gui_x86_64.elf`

At that time, a host Stage 3 compiler build was CPU-active and free disk was
about 8.9 GiB; a new QEMU run would have competed with it.  The preflight is
diagnostic status, not manual-real-screen proof.

## Forensic audit of the retained x86 attempt

The pre-existing x86 run is a FAIL and is not reusable evidence.  It was PID
`68860`, started `2026-07-30T12:49:04+09:00` with PPID 1, `-display cocoa`,
serial `.../serial-vfsfix.log`, and QMP
`.../qmp-vfsfix.sock`.  It ended during audit; the QMP socket was absent.  No
QMP command, injected input, process action, build, or VM launch was issued.

Its source worktree `/private/tmp/simple-qemu-live-20260730` was at
`23e6ba68f6058e19b8e5448024f29025a36c8879` and dirty
(`src/os/services/vfs/vfs_boot_init.spl`, an unrelated generated Gradle file,
and an untracked VFS test).  Its NVMe font image came from a separate worktree
at `eee12153a5c6e1e05466439f65f519ae27334568`.  This is mixed dirty-source
provenance, not a current admitted revision.

`serial-vfsfix.log` SHA-256:
`a8262af1620e0bb513ea66e8f719e0a939b8c8c40fbc849ff9173f258a98a915`.
It reached scanout/desktop initialization but recorded vector-font registration
of zero accepted faces, bitmap fallback, and
`HOST_GPU_NEGOTIATION_DONE ... result=fallback backend=software`, then
`runtime error: field access on nil receiver` and an exception frame.  It has
no WM-ready marker, requested/actual CPU-SIMD pair, positive native-SIMD hit,
physical input receipt, or timing/heap interval.  It fails REQ-QRS-001/002 and
cannot satisfy REQ-QRS-003 through REQ-QRS-008.

The EFI `EFI/BOOT/BOOTX64.EFI` was 21,901,312 bytes, mtime
`12:48:47+09:00`, SHA-256
`30a5485928f476ea9a9d5c197f2290638f4e04cb755f24cc1d85dbba5077f79f`;
`grub.cfg` names `SimpleOS WM 23e6ba6 vfsfix`.  No same-run `launch.env`,
`artifact-sha256.txt`, kernel ELF, or per-run manifest existed.  Font-image
SHA-256: `d26530c646b55a7068b86054c477f1f9e7dd4a6c60c83d1250f026fbc85cfaaf`.

`frame-v2.ppm`/`.png` and `manual/qemu-before-input.png` predate the launch
(`12:35` versus EFI `12:48` and QEMU `12:49`).  The PPM/PNG are 1280x800,
with SHA-256
`eb225c55dccae7843998d9d1812e60bae46271396779c0b6b39e9cdc17f93485` and
`1fdb7362d9ee04e82cddc52f25b11b709810154557d5965f6975fb46a352770c`.
The 3420x2214 manual PNG is SHA-256
`06031b69a27c01bef45c265887989bfd72fd9a9e65feca42d1bb54fe2cbbdaf0` and
visibly captures a Google Gemini window, not QEMU.  There is no matching
post-input capture or same-run generation; all are diagnostic only.

## Fail-closed admission and evidence rules

1. Allocate a new immutable
   `build/evidence/simpleos-qemu-wm-real-screen-<revision>-<utc-run-id>/` and
   fail if it exists.  Do not reuse the historical `build/qemu-live/evidence`.
2. Before launch, require a clean source revision and admitted self-hosted
   Simple binary; reject Rust seed/full-bootstrap substitutes and mixed
   revision ELF/EFI/font inputs.  Write `launch.env` and
   `artifact-sha256.txt` with source/artifact revision, full argv, QEMU
   version, CPU model/features, EFI/ELF/font hashes and evidence root.
3. Retain `-display cocoa`, serial-to-`<run>/serial.log`, and unique
   `-qmp unix:<run>/qmp.sock,server=on,wait=off`.  QMP may take frames for the
   manual lane but may not inject acceptance input.
4. Emit WM-ready only after a presentable first frame.  Fail on a guest fault,
   vector-font rejection/bitmap fallback, scalar/software/host-GPU fallback,
   missing positive SIMD evidence, or uncorrelated capture.
5. Serial must correlate monotonic `input_seq`, target/semantics and later
   frame generation for each manual action.  `interaction.env` records only
   operator timestamps/sequence IDs; serial remains authoritative.
6. `render.env` retains raw ten-frame intervals, p50/p95, QEMU CPU samples,
   and heap start/end/delta.  Retain process cleanup proof: no orphan QEMU
   process or reserved port remains after the owner closes its run.

## Required execution order

Run only from current `origin/main` in a clean isolated worktree with a
distinct artifact/cache/evidence root.  Do not start a VM until selected-row
transport and every identity are READY.

1. Confirm disk headroom and that no host bootstrap/native build writes the
   guest cache; confirm exclusive QEMU ownership.
2. Run the SIMD prerequisite once:

   ```sh
   sh scripts/check/check-simpleos-qemu-engine2d-simd-kernels.shs
   ```

3. Materialize required x86_64/AArch64 artifacts incrementally, without full
   bootstrap.  Build the AArch64 desktop path through:

   ```sh
   sh scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs
   ```

4. Re-run aggregate preflight once:

   ```sh
   sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --preflight
   ```

5. Before a manual x86 run, execute the static route checks:

   ```sh
   sh scripts/check/check-simpleos-x86-64-wm-qemu-preflight.shs
   SIMPLE_LIB=src bin/simple test test/03_system/gui/x86_64_wm_qemu_preflight_spec.spl --mode=interpreter
   ```

   They must report static pass and `live_qemu=not-started-host-gate`; they do
   not satisfy REQ-QRS.
6. Run automated diagnostic/compatibility wrappers at most once when their
   selected artifact and transport are ready:

   ```sh
   sh scripts/check/check-simpleos-x86-64-wm-render-event-evidence.shs
   sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs
   sh scripts/check/check-simpleos-arm64-qmp-input-evidence.shs
   ```

   Their QMP-injected events remain automated evidence only.  Preserve their
   reports; stop after first real failure and never replace a failed backend
   with software.
7. For REQ-QRS, after all manual gates are ready, the user physically performs
   click, title-bar drag, `a`, Ctrl press, Ctrl release in the visible Cocoa
   QEMU window.  Capture before/after QMP and macOS QEMU-window images, then
   finalize `interaction.env` and `render.env`.  Reject synthetic source,
   missing serial-frame correlation, unchanged drag/frame, or a non-QEMU
   macOS capture.

## Architecture blockers and remaining work

- Keep x86_64 and RISC-V rows BLOCKED until the VirtIO-serial transport is
  implemented or formally retained; AArch64 evidence cannot claim those rows.
- Diagnose the retained x86 nil receiver and vector-font rejection before its
  next bounded live run.  Vector-font identity/glyph material must be accepted,
  never silently replaced by bitmap fallback.
- Finish current AArch64/HVF artifact admission, then run its production
  ordered-event lane under the sole-owner/no-orphan rule.
- At audit time this sparse integration checkout omitted canonical paths that
  exist on current `origin/main`; use a checkout containing them.  The
  integration worktree also had unrelated dirty files, none overwritten by
  this plan.

## Canonical references on origin/main

- `scripts/check/check-simpleos-x86-64-wm-qemu-preflight.shs` and
  `test/03_system/gui/x86_64_wm_qemu_preflight_spec.spl` — static production
  entry/theme/SIMD/frame/event route.
- `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` and
  `test/03_system/check/simpleos_wm_fullscreen_evidence_simple_bin_spec.spl`
  — artifact admission/provenance and automated QMP correlation; its F11 and
  pointer injection are not physical-manual evidence.
- `test/03_system/os/qemu/qmp_screendump_spec.spl` — QMP screendump failure
  contract.  `test/03_system/gui/wm_input_qemu_smoke_spec.spl` is a separate
  synthetic smoke and must not be relabeled as manual input evidence.
