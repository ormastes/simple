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

- QEMU process and port discovery;
- guest image/kernel selection and construction;
- SIMD prerequisite execution;
- QEMU launch, diagnostic QMP input injection, physical-input evidence,
  capture, shutdown, and cleanup;
- evidence correlation and the final PASS/FAIL report.

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

QMP input injection is diagnostic coverage only. Final real-screen acceptance
uses physical input performed by the user in the visible Cocoa window; QMP is
used for framebuffer capture and correlation, not to manufacture the accepted
click, drag, text, or modifier events.

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
8. Preserve all serial, QMP, argv, manifest, capture, checksum, timing, and
   process-cleanup evidence. Stop after the first real failure; do not retry or
   replace a failed backend with software.

## 2026-07-30 physical real-screen and performance amendment

The current x86_64 run established a measured before-fix baseline:

- a 1,708,408-byte font load produced 41,314 scalar scratch-cluster reads;
- serial output grew to 1.77 MiB;
- the guest bump heap reached `0x1ffff7a0` of its `0x20000000` limit and
  panicked before a complete frame;
- visible output was a partial baremetal framebuffer, without positive
  `cpu_simd` execution counters.

The packed-byte VFS correction reduced serial output to 10.8 KiB and first-frame
heap use to approximately 193 MiB without increasing the heap or removing the
font. That improvement is accepted as a focused boot-I/O/memory result, but the
run remains a render FAIL because `FontRenderer.has_sffi_ttf` then encountered
a nil receiver before complete-frame, SIMD, or physical-input evidence.

The next authorized live run must also satisfy:

- boot-to-paint-complete <=30 seconds (`NFR-E2D-QEMU-001`);
- font data-cluster reads equal
  `ceil(font_bytes / cluster_bytes)`, plus bounded FAT/directory metadata reads;
- one file-chain summary and failure-only detail, with no per-cluster success
  logging;
- guest heap high-water <=256 MiB before the first complete frame and no
  positive growth across ten changed interaction frames;
- after one warm-up, ten changed frames report render/present p50 and p95, with
  p95 <=33.4 ms (30 FPS);
- no filesystem scan, font reload, or fresh framebuffer-sized allocation in
  the input/redraw loop.

## Acceptance gates

A target passes only when one correlated run proves all of the following:

- the selected backend and guest transport are real and fail closed;
- the captured screen is produced by the canonical WM -> Draw IR -> Engine2D
  guest path, not by a synthetic image or CPU/software fallback;
- a positive initial frame ID, checksum, dimensions, and presentation receipt
  agree across guest serial, host/QEMU evidence, and capture;
- the physical ordered event sequence contains
  `focus,pointer_move,pointer_down,pointer_move,pointer_up,key_down,key_up,`
  `text_commit,ctrl_down,ctrl_up`; diagnostic QMP events are labeled separately
  and cannot satisfy this row;
- each accepted semantic action advances the expected state/frame generation;
- before/after captures differ at the expected semantic region;
- vector-font identity and glyph material are accepted rather than silently
  replaced with a bitmap fallback;
- SIMD prerequisites pass for the guest architecture, while the live render
  independently proves the pixels;
- QEMU argv, accelerator, guest artifact hashes, revision, timing, maximum RSS,
  guest heap high-water, boot-I/O counts, frame p50/p95, and clean shutdown are
  retained;
- no orphan QEMU process or reserved port remains.

`BLOCKED`, `unsupported`, compile-only output, source inspection, screenshots
without receipts, software fallback, and historical captures do not satisfy
this plan.

## Immediate remaining work

1. Let the active host compiler build release CPU and disk pressure.
2. Have the sole QEMU owner construct and attest the missing AArch64 artifacts
   incrementally.
3. Fix or formally retain the x86_64/RISC-V VirtIO-serial transport blocker;
   do not claim those rows from AArch64 evidence.
4. Diagnose the retained `FontRenderer.has_sffi_ttf` nil receiver and
   vector-font rejection without another live launch; authorize a new bounded
   run only after focused native evidence identifies and fixes that owner.
5. Execute the AArch64/HVF render-and-event run and publish its correlated
   evidence.

Merge owner and final reviewer: root/high-capability Codex agent. QEMU launch
owner: one explicitly assigned QEMU agent session only.

## 2026-07-30 sole-owner session 2 (later same day) — fail-closed, no launch

A second sole-owner QEMU session picked up this plan at approximately
`2026-07-30T04:07Z`. It re-verified environment state before doing anything
that could start a VM or write large artifacts, per the "Required execution
order" step 1 gate ("Confirm disk headroom ... confirm exclusive QEMU
ownership").

Findings:

- **Disk headroom regressed below safe margin.** `df -g /Users/ormastes`
  reported **3 GiB available** (down from the 8.9 GiB recorded in the
  preflight earlier the same day). This repo has a documented history of
  repeated ENOSPC incidents; writing a new QEMU disk image, FAT32 artifact, or
  running an incremental compiler build at 3 GiB free was judged unsafe.
- **A host compiler build is still CPU-active**, confirmed via `ps aux`: a
  `rustc --crate-name simple_compiler ... -C opt-level=z` process (PID 4881)
  competing for CPU, matching the exact condition the morning preflight
  already flagged as a reason not to start a competing QEMU run.
  `build/bootstrap` alone is 7.8 GiB, consistent with the tight remaining
  headroom.
- **None of the five canonical artifacts listed as missing in the morning
  preflight have appeared since**: `build/os/simpleos_x86_64_host_gpu_probe.elf`,
  `build/os/simpleos_arm64_host_gpu_probe.elf`,
  `build/os/simpleos_arm64_desktop_engine2d.elf`, the AArch64 desktop build
  manifest / `fat32-arm64-desktop.img`, and `simpleos_desktop_gui_x86_64.elf`
  are all still absent from the tree.
- No `build/evidence/simpleos-qemu-wm-real-screen-*` directory was created —
  none existed at session start and none was created this session.
- Per the working-copy state at session start, `jj`'s workspace was **stale**
  (last synced at an old operation) and the plan file itself was missing from
  the checked-out working copy until `jj workspace update-stale` +
  `jj rebase -d main@origin` were run to reach current `origin/main`
  (`5d6c2259`). This is recorded here because it means any session that
  skipped that step would have been silently working from a stale tree
  lacking this very plan.

Decision: **fail closed, do not launch.** Per the plan's own "Required
execution order" step 1 and the "Fail-closed admission and evidence rules",
this session did not run the SIMD prerequisite, did not build any AArch64 or
x86_64 artifact, did not run `check-simpleos-qemu-host-gpu-2d.shs
--preflight` again (it would not change the disk/CPU-contention verdict and
the plan caps some of these wrappers to "at most once"), and did not open a
QEMU process, QMP socket, or new evidence directory. No REQ-QRS row (001
through 008) was attempted or satisfied this session. Nothing was deleted or
rebuilt to free space, per the standing instruction not to delete build
artifacts belonging to other in-flight sessions.

Recommended next step for the next sole-owner session: wait for the active
host compiler build to finish and for free disk to return to a safe margin
(the morning run treated 8.9 GiB as marginal; 3 GiB is not workable), then
resume at "Required execution order" step 2 (SIMD prerequisite) followed by
step 3 (incremental AArch64 desktop artifact build) — do not repeat the disk
work already known to be blocked.

## 2026-07-30 delegated-task checkpoint — origin/main 7d6cfd0e

Delegation revision:
`7d6cfd0edd8421664a1ec5a48b4e8a46930fe2d7`.

Ownership:

- The delegated QEMU agent is the sole execution owner for this lane,
  including its scoped build, launch, evidence, cleanup, and failure report.
- `/root` is the merge and push owner.
- No one-time gate has been consumed by this delegated task.

Current external ownership conflicts prevent execution:

- QEMU PID `95929` owns the existing Cocoa/`qmp-final` lane.
- Bootstrap chain PIDs `99509`, `99657`, `99658`, and `99663` own the
  competing bootstrap/native-build work.
- The delegated owner must not stop, inject, reuse, or collide with those
  processes, their sockets, caches, or evidence paths.

Exact next task after all listed processes clear:

1. Recheck that no external QEMU, bootstrap, or native-build process remains,
   then refresh the clean isolated QEMU worktree to live `origin/main`.
2. Run the SIMD prerequisite exactly once:

   ```sh
   sh scripts/check/check-simpleos-qemu-engine2d-simd-kernels.shs
   ```

3. Only when an admitted current pure-Simple `bin/simple` is available, run
   the canonical x86 static preflight and its spec exactly once:

   ```sh
   sh scripts/check/check-simpleos-x86-64-wm-qemu-preflight.shs
   SIMPLE_LIB=src bin/simple test test/03_system/gui/x86_64_wm_qemu_preflight_spec.spl --mode=interpreter
   ```

   A Rust seed or stale/unadmitted binary is not an allowed substitute.
4. Run the aggregate preflight exactly once:

   ```sh
   sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --preflight
   ```

5. If admission is blocked, identify and fix one smallest host-independent
   source/script blocker and add a discriminating focused test. Do not broaden
   the change or run a full bootstrap.
6. Launch at most one bounded VM only if the selected artifact, transport,
   provenance, and ownership gates are all READY. Preserve no-orphan cleanup
   evidence.
7. Physical Cocoa click/drag/typing/Ctrl evidence remains a manual user action.
   Synthetic QMP, AppleScript, or other injected input is diagnostic only and
   is inadmissible for REQ-QRS-004 through REQ-QRS-007.

## 2026-07-30 — task dispatch to the sole QEMU owner (session 3 handoff)

This section is the task assignment. Per the project owner's direction, QEMU
work is dispatched **only through this document**, and is executed by exactly
**one** agent session at a time. Do not launch QEMU from any other session.

### What changed since session 2's fail-closed verdict

- **The ENOSPC risk session 2 flagged actually fired.** Free disk reached
  **0 GiB**. `git prune` then aborted with `fatal: bad tree object
  0b9d64735680743c2f4db53618b67b424c94f7b3`, and two independent agent
  sessions reported `jj` fully broken (`Object ... not found`, missing
  working-copy commit) plus dangling refs whose target objects are absent from
  the local object store. **The local repository has object-level corruption.**
  All landed work is safe at `origin/main` and was content-verified there;
  nothing is lost. But local `jj` is unreliable — use plain `git`
  (fetch/commit/push) until the repo is repaired.
- **Partial recovery to ~6 GiB free**, achieved only by removing
  `build/worktrees/stage4-2b6ca665` after verifying it had zero uncommitted
  changes and a HEAD already contained in `origin/main`. The other 23
  worktrees were deliberately left untouched: each has either uncommitted
  changes or a HEAD not in `origin/main`, i.e. other sessions' unpushed work.
  **Do not delete them to make room.**
- **6 GiB is still not a safe margin.** Session 2 correctly treated 8.9 GiB as
  marginal. A cold real-screen run needs a full artifact build plus framebuffer
  captures. Reclaiming a further ~5.2 GiB is pending a decision by the project
  owner on an unversioned tree outside the repo; that decision is theirs, not
  an agent's.

### Blocking preconditions — verify each before any build or launch

1. Free disk at a genuinely safe margin (> 8.9 GiB), re-checked immediately
   before the build **and** again before launching QEMU. Fail closed if it
   regresses mid-run; do not push through ENOSPC. It has already corrupted the
   repo once today.
2. No competing host compiler build active (session 2 found `rustc
   --crate-name simple_compiler`, PID 4881). Do not kill a peer's build — wait.
3. The five canonical artifacts listed in session 2's entry still absent → they
   must be built at step 3, not assumed present.
4. Confirm sole QEMU ownership. An unrelated peer `qemu-system-x86_64` may be
   running for different work: **do not kill it, do not reuse it**, and account
   for its CPU/disk contention.

### Assigned work, in order

Resume at "Required execution order" step 2 — do **not** repeat the disk/CPU
diagnosis already established as blocked twice today.

- Step 2: SIMD prerequisite. REQ-QRS-002 requires same-run
  `requested=cpu_simd`, `actual=cpu_simd`, CPU feature/profile, a positive
  native SIMD hit count, and no fallback marker. Per the fail-closed rules, a
  CPU-looking image with zero SIMD hits or any fallback marker is a **failure**
  — report it as such, do not soften it.
- Step 3: incremental artifact build. Pin the compiler explicitly. It must be
  an **admitted pure-Simple** binary, never the Rust seed. Note the hazard:
  several wrappers auto-detect and prefer `build/bootstrap/stage2/*/simple`
  over `bin/release/*/simple`, and that stage2 binary's version string
  `simple-bootstrap 1.0.0-beta` passes filters that reject only
  `*bootstrap*seed*`. Record the binary path + sha256 + version in the
  evidence. Do not run a full bootstrap; do not `cargo clean`.
- Steps 4–7: boot via real OVMF pflash into a visible Cocoa window (never
  `-kernel` semantics, never `isa-debug-exit`), capture pre-input framebuffer
  and macOS window, open the serial evidence interval.

### Human-input boundary — plan for it explicitly

REQ-QRS-004 through REQ-QRS-007 **cannot be satisfied by any agent**. The plan
forbids synthetic input for acceptance: QMP `send-key`, mouse injection, and
AppleScript are all disallowed. Therefore:

- Complete REQ-QRS-001, 002, 003 and 008 autonomously.
- Then **stop with the QEMU instance alive and the serial interval open**, and
  hand the project owner numbered instructions for the five physical actions in
  order (click the showcase, drag its title bar, type `a`, press Ctrl, release
  Ctrl), naming the exact window to act on.
- Only after they confirm, capture the post-input framebuffer and window, and
  correlate each accepted input sequence with a **later** frame generation.

### Reporting contract

Report per-REQ-QRS status as satisfied / pending-human-input / failed, with the
evidence path for each. A precise negative result is a valid outcome; a vague
or overstated positive is not. Evidence directories and reports stay **out of
git** (repo rule: do not add reports to git unless requested) — this plan doc
and any `.shs`/`.spl` runner do get committed. No Bash, no Python.
