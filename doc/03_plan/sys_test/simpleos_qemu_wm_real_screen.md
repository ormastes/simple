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

Exactly one delegated QEMU execution agent session owns QEMU process/port
discovery, launch, captures, evidence directory, shutdown, and the live failure
report. Non-launch prerequisite agents may prepare attested guest artifacts,
focused native regressions, and source-only transport designs, but they must
not start QEMU, open QMP, reserve a VM port, or write the live evidence root.
Live ownership transfers explicitly before a different session launches QEMU.
Only one bounded live run per architecture is allowed after prerequisites;
there is no automatic retry. Preserve and review a failure before authorizing
another run.

- The delegated QEMU execution agent alone owns launch/runtime evidence.
- Named prerequisite agents own only the files and bounded checks assigned in
  the delegated-task matrix below.
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

The automated AArch64 diagnostic lane has a separate, non-physical acceptance
contract.  These rows are prerequisites for artifact admission and diagnostic
QMP evidence; they cannot satisfy `REQ-QRS-004` through `REQ-QRS-007`.

| ID | Required proof |
|---|---|
| REQ-AQMP-001 | The selected current self-hosted compiler is bound by SHA-256 to a `status=pass` Stage 2/Stage 3 provenance manifest containing admitted Stage 2 identity, Stage 2 and Stage 3 sanity PASS, source fingerprint, command transcripts, and Stage 3 output identity. A mechanically usable early-phase artifact is admissible only when this provenance is complete and clean; copying or renaming an older binary is forbidden. |
| REQ-AQMP-002 | The same artifact build runs with stub fallback disabled and the strict fabricated-stub ratchet enabled, records `Fabricated freestanding stubs: 0 symbol(s)`, and fails closed on `FABRICATED-NEW`, unmeasured fabrication, or a missing baseline. |
| REQ-AQMP-003 | One bounded live run binds the admitted compiler, guest source, kernel, disk, and disk producer identities to serial receipts, ordered QMP `input-send-event` sequences, guest frame/RAMFB commit revisions and checksums, and distinct before/after QEMU RAMFB screendumps. |

| Requirement | Executable acceptance artifact | Retained evidence | Current status |
|---|---|---|---|
| REQ-AQMP-001 | `test/03_system/os/wm/arm64_simpleos_qmp_input_spec.spl` checks the Stage 2/3 manifest fields, compiler admission, and build-manifest compiler identity contract. | Stage 2/3 `provenance.env`, sanity evidence, command transcripts, selected compiler SHA-256, ARM64 build manifest and frozen-source manifest. | Pending a current producer receipt; source contract present. |
| REQ-AQMP-002 | The same spec checks no-stub environment flags, the literal zero-fabrication receipt, self-test rejection fixtures, and fail-closed rejection reason. | Canonical build log plus its SHA-256 and the ARM64 build manifest. | Pending a current canonical build; source contract present. |
| REQ-AQMP-003 | The same spec's live scenario invokes the canonical wrapper; `arm64_wm_ramfb_screendump_spec.spl` covers live RAMFB capture and the wrapper correlates QMP input, serial receipts, guest frames, and captures. | Serial/QMP logs, before/after PPMs and SHA-256 values, correlation report, manifest/frozen-source identities, launch hashes, and cleanup receipt from one run root. | Pending one admitted live run; no historical or source-only evidence is PASS. |

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
   SIMPLEOS_ARM64_ATTESTED_COMPILER=/absolute/path/to/stage3/simple \
   SIMPLEOS_ARM64_COMPILER_RECEIPT=/absolute/path/to/compiler-receipt.env \
   SIMPLEOS_ARM64_STAGE3_PROVENANCE=/absolute/path/to/stage3/provenance.env \
     sh scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs
   ```

   The producer and QMP consumer both validate the exact canonical Stage 3
   manifest against the clean source root. A custom smoke receipt alone is not
   sufficient; absence of a current Stage 3 provenance chain is a blocker.

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

## 2026-07-30 delegated non-launch task matrix

These assignments let multiple agents prepare independent prerequisites while
preserving one sole live-QEMU session. None of A-GUEST, Q-NIL, Q-FONT, or
Q-TRANSPORT may launch QEMU, open QMP, build a live evidence directory, run a
full bootstrap, or push. `/root` owns integration, verification, and push.

| Lane | Assigned agent scope | Start dependency | Required deliverable |
|---|---|---|---|
| A-GUEST | Incremental guest artifact construction and attestation | Host compiler/native build finished; safe disk; current admitted non-symlink pure-Simple compiler; SIMD prerequisite PASS | Artifact receipt plus required x86_64/AArch64 ELFs, disk image, and manifests |
| Q-NIL | `FontRenderer.has_sffi_ttf` nil-receiver root cause and native regression | None; independent of VM and guest build | Focused Cranelift native regression and appended compiler bug evidence |
| Q-FONT | Vector-font `accepted=0` and bitmap-fallback repair proof | Q-NIL PASS or conclusive receiver-channel clearance | Non-QEMU VFS/font native evidence report with positive vector identity and glyph batch |
| Q-TRANSPORT | x86_64/RISC-V VirtIO-serial transport review and implementation decomposition | None; runs in parallel with Q-NIL | Transport bug/design report plus bounded source-only checks |
| Q-LIVE | Sole QEMU execution, QMP/capture/physical-input handoff, cleanup, final evidence | Applicable prerequisite receipts reviewed and merged; one target row READY | One bounded correlated live evidence bundle |

### A-GUEST — artifact-preparation agent

The assigned artifact agent uses a clean isolated full checkout at current
`origin/main`, a distinct cache, and one bounded attempt per command. It stops
after receipt handoff and never starts QEMU.

Prerequisite:

```sh
sh scripts/check/check-simpleos-qemu-engine2d-simd-kernels.shs
```

Construction:

```sh
SIMPLE_BIN=/absolute/path/to/admitted/pure-simple/compiler
COMPILER_RECEIPT=/absolute/path/to/simpleos-arm64-compiler-receipt.env
mkdir -p build/os/generated/generated build/os
cp src/generated/simpleos_log_config.spl build/os/generated/generated/simpleos_log_config.spl
SIMPLE_BOOT_MINIMAL=1 SIMPLE_OS_LOG_MODE=on "$SIMPLE_BIN" native-build --source build/os/generated --source src/os --source src/lib --source examples/09_embedded/simple_os --backend cranelift --cpu x86-64-v1 --opt-level=aggressive --log on --timeout 870 --entry-closure --entry examples/09_embedded/simple_os/arch/x86_64/host_gpu_smoke_entry.spl --target x86_64-unknown-none -o build/os/simpleos_x86_64_host_gpu_probe.elf --linker-script examples/09_embedded/simple_os/arch/x86_64/linker.ld
env -u SIMPLE_BINARY -u SIMPLE_BIN -u SIMPLE_FRONTEND_DELEGATE -u SIMPLE_BOOTSTRAP_DRIVER SIMPLE_OS_BUILD_BACKEND=llvm SIMPLE_OS_LOG_MODE=off SIMPLE_OS_BUILD_TIMEOUT_MS=900000 "$SIMPLE_BIN" os build --scenario=x64-desktop-gui
SIMPLE_BOOT_MINIMAL=1 SIMPLE_OS_LOG_MODE=on "$SIMPLE_BIN" native-build --source build/os/generated --source src/os --source src/lib --source examples/09_embedded/simple_os --backend cranelift --opt-level=aggressive --log on --timeout 870 --entry-closure --entry examples/09_embedded/simple_os/arch/arm64/host_gpu_file_backed_ram_tail_smoke_entry.spl --target aarch64-unknown-none -o build/os/simpleos_arm64_host_gpu_probe.elf --linker-script examples/09_embedded/simple_os/arch/arm64/linker.ld
SIMPLEOS_ARM64_ATTESTED_COMPILER="$SIMPLE_BIN" \
SIMPLEOS_ARM64_COMPILER_RECEIPT="$COMPILER_RECEIPT" \
    sh scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs
```

The compiler receipt uses schema `simpleos-arm64-compiler-receipt-v1` and pins
the compiler's absolute path, SHA-256 identity, and live `--version` output. It
must also record `native_smoke_status=pass`, `stub_fallback=forbidden`,
`fabricated_stub_status=none`, and `measurement_status=measured`. The producer
runs with `SIMPLE_NO_STUB_FALLBACK=1` and the strict fabricated-stub ratchet,
captures its build log, and publishes no manifest if the log reports fabricated,
unmeasured, unbaselined, or weak-zero fallback bodies.

Required handoff:

- `simpleos_x86_64_host_gpu_probe.elf`,
  `simpleos_desktop_gui_x86_64.elf`, and its build stamp;
- `simpleos_arm64_host_gpu_probe.elf`,
  `simpleos_arm64_desktop_engine2d.elf`, `fat32-arm64-desktop.img`,
  `make_os_disk`, build manifest, and frozen-source manifest;
- exact revision, compiler receipt path/hash, compiler path/version/hash,
  commands, sizes, and 64-hex
  SHA-256 identities for every compiler, ELF, disk, and font input;
- focused x86 ELF checks and current-source/manifest identity checks.

Stop on the first real failure and preserve cache/logs. Artifact construction
does not clear the x86/RISC-V `virtio-serial-unimplemented` blocker.

### Q-NIL — nil-receiver agent

Inputs:

- `/private/tmp/simple-qemu-live-20260730/build/qemu-live/evidence/serial-vfsfix.log`
  (SHA-256
  `a8262af1620e0bb513ea66e8f719e0a939b8c8c40fbc849ff9173f258a98a915`);
- retained x86 ELF
  `/private/tmp/simple-qemu-live-20260730/build/qemu-live/out/simpleos_wm_vfsfix_final_23e6ba6.elf`;
- `llvm-addr2line` mapping of RIP `0x086cf92a` to
  `FontRenderer.has_sffi_ttf`;
- `src/lib/nogc_sync_mut/text_layout/font_renderer.spl`,
  `src/compiler/70.backend/**`, and the existing aggregate-return/font-cache
  bug reports.

Deliver one minimal native regression under `test/02_integration/rendering/`
that stores/returns `FontRenderer` and proves its `has_sffi_ttf` receiver is
non-nil and correctly placed. Append root cause and evidence to the existing
compiler bug report. Run one clean current-origin Cranelift native build/run
and at most one fix/retest cycle. Do not bootstrap or launch a VM.

### Q-FONT — vector-font agent

Start only after Q-NIL passes or conclusively clears the receiver channel.
Use the same staged VFS bytes/path aliases as the failed guest, retaining the
serial facts: zero accepted faces, a 1,708,408-byte read, then bitmap fallback.

The non-QEMU native fixture must prove:

- accepted candidate count is positive and every required pin is accepted;
- selected vector identity survives registry read-back;
- a non-empty glyph batch is produced;
- bitmap fallback is rejected.

Run the focused font-asset staging and `FontRenderer` specs once each. Write
`doc/09_report/simpleos_qemu_font_registration_native_evidence_2026-07-30.md`
with revision, exact command, binary/input hashes, identity/count/glyph
receipts, and any focused repair.

### Q-TRANSPORT — transport-review agent

Review the wrapper transport classifier, guest ivshmem owners, WM executor,
shared protocol, and QEMU system spec. Write
`doc/08_tracking/bug/simpleos_qemu_virtio_serial_host_gpu_transport_2026-07-30.md`
covering device availability, the missing framed guest adapter/host endpoint,
framing and correlation, timeouts, interrupt/queue ownership, and an
implementation/test decomposition.

Run only:

```sh
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --self-test-qemu-accel
SIMPLE_LIB=src bin/simple test test/03_system/os/qemu/simpleos_qemu_host_gpu_2d_spec.spl --mode=interpreter
```

Do not run `--preflight`, build a guest, weaken the
`virtio-serial-unimplemented` result, or claim AArch64 file-backed RAM covers
x86_64/RISC-V.

### Dependency and handoff

```text
Q-NIL ──> Q-FONT ─────────────┐
A-GUEST ──────────────────────┼──> /root review ──> Q-LIVE sole executor
Q-TRANSPORT ──> x86/RV READY ─┘
```

A-GUEST and Q-TRANSPORT may run in parallel with Q-NIL. Q-FONT waits for
Q-NIL. Q-LIVE starts only after the applicable artifacts and blocker repairs
are reviewed and the selected preflight row is READY. Exactly one Q-LIVE
session owns every VM launch, port, capture, input interval, shutdown, and
no-orphan proof.

## 2026-07-30 delegated-lane execution checkpoint

### Q-TRANSPORT — completed and reviewed

The non-launch transport review is published at commit
`49052de2284972e24a1b437f60936286a8da81d4`:

```text
doc/08_tracking/bug/simpleos_qemu_virtio_serial_host_gpu_transport_2026-07-30.md
```

The QEMU acceleration self-test passed once. The interpreter system spec was
not executed because the isolated checkout intentionally had no admitted
`bin/simple`; no bootstrap or retry was used. The report keeps x86_64 and
RISC-V `virtio-serial-unimplemented`, defines the missing 64-byte framed
transport, socket endpoint, correlation/deadline policy, per-ISA queue/IRQ
ownership, and implementation/test decomposition. It does not authorize a VM
launch or claim AArch64 evidence for another ISA.

### Q-NIL — preserved, blocked before probe execution

The retained serial checksum matches this plan. `llvm-addr2line` maps RIP
`0x086cf92a` to `FontRenderer.has_sffi_ttf+0x32`, its explicit nil-receiver
trap path. The two direct callers pass tuple-extracted receiver stack slots.

The assigned agent prepared this exact-shaped non-QEMU regression:

```text
/private/tmp/simple-q-nil-20260730.YDdE5k/test/02_integration/rendering/font_renderer_receiver_native_probe.spl
SHA-256 2257670baf4a416a6d9f08061e27dbe64912c2f1907e0a011df6fe718eae7f78
```

It covers both retained consumer shapes: `(FontRenderer,text,bool)` and
`(FontRenderer,bool)` returns/extractions, handle placement, and
`has_sffi_ttf`. The probe is deliberately uncommitted and is not PASS evidence
because its single allowed native build stopped before probe code generation.

Attempted once:

```sh
env SIMPLE_NO_STUB_FALLBACK=1 /Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple native-build --source src/lib --source test/02_integration/rendering --backend cranelift --entry-closure --entry test/02_integration/rendering/font_renderer_receiver_native_probe.spl --output build/q_nil/font_renderer_receiver_native_probe
```

The July 25 deployed compiler cannot parse current-origin
`src/lib/skia/feature/shaper/ot_layout_gpos.spl` multiline forms at lines 268,
289, 395, 452, and 687. No binary was produced. The retry was preserved rather
than wasted with the same stale compiler.

Q-NIL may resume only after a current-origin self-hosted compiler is admitted.
It must then execute this hashed probe once before any source fix or Q-FONT
claim. Q-FONT remains waiting; A-GUEST also remains waiting for the admitted
compiler. Q-LIVE remains unauthorized and no QEMU/QMP process was launched by
these delegated lanes.

## 2026-08-01 AC-2 / AC-3 current-evidence audit and resume handoff

This is an evidence audit, not a new live-run claim.  At reviewed revision
`9892b6f51fd71ac4095b73da6e64272e109087db`, the guest-side WM/theme, Draw IR,
Engine2D frame, serial-receipt, capture-correlation, and event-route source
wiring is present.  That source state establishes the AC-2 wiring prerequisite
only; it does **not** establish AC-3.  No current source-matched admitted
ELF/FAT32 artifact and no current correlated live-QEMU evidence bundle have
been retained, so every live row remains pending.

| Acceptance row | Current evidence | Status | Boundary that remains |
|---|---|---|---|
| AC-2 — guest WM/theme/render/event wiring | Canonical source routes and the static preflight/spec references listed above; the current theme propagation repair is source-level only. | Wired, not live-proven | A current admitted guest artifact must exercise the route through a visible guest frame. |
| AC-3 — x86_64 live render/events | The transport classifier and reviewed bug report preserve the negative result. | BLOCKED | `virtio-serial-unimplemented`; x86_64 cannot borrow AArch64 RAM-tail evidence. |
| AC-3 — RISC-V live render/events | The same classifier and bug report preserve the negative result. | BLOCKED | `virtio-serial-unimplemented`; requires the framed VirtIO serial adapter and its per-ISA queue/IRQ proof. |
| AC-3 — AArch64/HVF live render/events | File-backed-RAM-tail source/wrapper path exists. | PENDING | Build and admit the current ARM64 ELF/FAT32/manifest set, then obtain the required physical Cocoa-input interval. |

The retained evidence is deliberately negative/diagnostic and must remain
available to the next owner: the 2026-07-30 x86 serial log
`serial-vfsfix.log` (SHA-256
`a8262af1620e0bb513ea66e8f719e0a939b8c8c40fbc849ff9173f258a98a915`), its
mixed-provenance EFI/font identities recorded above, the unexecuted Q-NIL
probe at `/private/tmp/simple-q-nil-20260730.YDdE5k/test/02_integration/rendering/font_renderer_receiver_native_probe.spl`
(SHA-256 `2257670baf4a416a6d9f08061e27dbe64912c2f1907e0a011df6fe718eae7f78`),
and the transport design/negative classification in
`doc/08_tracking/bug/simpleos_qemu_virtio_serial_host_gpu_transport_2026-07-30.md`.
They are failure-analysis inputs, never artifact admission or screenshot proof.

### Exact resume sequence

Q-LIVE is the sole launch/capture/process-cleanup owner.  A-GUEST owns the
artifact receipt only; Q-TRANSPORT owns the x86_64/RISC-V blocker repair and
its source-only checks. `/root` remains merge owner, and a separate
high-capability Codex reviewer is the final reviewer for provenance, manual
input separation, and per-row conclusion.  No other agent may start QEMU,
open QMP, reuse a socket, or write the run evidence root.

After a clean current-origin isolated worktree has an admitted pure-Simple
compiler, sufficient disk headroom, and no competing QEMU/build owner, run
each bounded prerequisite once in this order:

```sh
git fetch origin main
git worktree add --detach /private/tmp/simple-qemu-live-<utc-run-id> origin/main
cd /private/tmp/simple-qemu-live-<utc-run-id>
test -z "$(git status --porcelain)"
sh scripts/check/check-simpleos-qemu-engine2d-simd-kernels.shs
sh scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --preflight
SIMPLEOS_ARM64_QMP_EVIDENCE_DIR=build/evidence/simpleos-qemu-wm-real-screen-9892b6f51f-<utc-run-id>/diagnostic-qmp sh scripts/check/check-simpleos-arm64-qmp-input-evidence.shs
```

The final command is diagnostic QMP evidence only.  It cannot satisfy the
physical-input rows.  Its admitted build inputs must be retained at the same
run root: `simpleos_arm64_desktop_engine2d.elf`,
`fat32-arm64-desktop.img`, `make_os_disk`,
`simpleos_arm64_desktop_engine2d.build-manifest.env`, its frozen-source
admission manifest, compiler path/version/SHA-256, command, `launch.env`,
`artifact-sha256.txt`, serial/QMP logs, before/after framebuffer captures,
macOS QEMU-window captures, `interaction.env`, `render.env`, and no-orphan
cleanup receipt.

Only after that admission reaches READY may Q-LIVE launch one visible ARM64
Cocoa QEMU instance with the serial interval open.  The project owner must
then physically perform, in order, the visible-window click, title-bar drag,
`a` keypress, Ctrl press, and Ctrl release.  Q-LIVE captures the later frame
and finalizes the correlation; QMP/AppleScript/synthetic events remain marked
diagnostic.  Until that human interval exists, ARM64 AC-3 is pending even when
the diagnostic wrapper passes.

For x86_64 and RISC-V, do not run a live retry after the sequence above. Resume
only after Q-TRANSPORT implements and tests the framed VirtIO serial endpoint;
then run the retained required source checks exactly once before a new
preflight:

```sh
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --self-test-qemu-accel
SIMPLE_LIB=src bin/simple test test/03_system/os/qemu/simpleos_qemu_host_gpu_2d_spec.spl --mode=interpreter
sh scripts/check/check-simpleos-qemu-host-gpu-2d.shs --preflight
```

`virtio-serial-unimplemented` remains the correct fail-closed outcome until
those checks and a fresh admitted per-ISA artifact exist.

### x86 Engine2D screenshot boundary

`scripts/check/check-simpleos-wm-visible-display-evidence.shs` and
`test/03_system/gui/gui_entry_engine2d_wm_simple_web_spec.spl` build
`examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl`. That
target proves the generated Aetheric baseline and WM/Web/Engine2D scene, but
does not mount media or read `/THEME.CSS`; its UEFI image stages only the
kernel. It must not be cited as custom Stitch/glass CSS evidence.

The full x86 desktop entry has the required VFS override order. Extending the
Engine2D screenshot target is an explicit F-2 requirement choice in
`doc/02_requirements/feature/wm_theme_qemu_options.md`:

- F-2 A: add the shared mounted CSS contract to every QEMU capture target;
- F-2 B: retain the small baseline demo and restrict custom CSS claims to the
  full desktop entry.

Until selection, this row remains `baseline-only`, not `PASS` or `blocked`.

### AArch64 compiler admission boundary

The ARM64 attested-build wrapper requires an explicit current self-hosted
compiler and a matching immutable receipt through
`SIMPLEOS_ARM64_ATTESTED_COMPILER` and `SIMPLEOS_ARM64_COMPILER_RECEIPT`.
The receipt pins path, SHA-256 and live version output and records a passing
native smoke, forbidden stub fallback, no fabricated stubs, and measured
status. A stale release, Rust seed, renamed binary, or an artifact whose build
reported fabricated weak-zero bodies must not be admitted. Resume only after a
new provenance-qualified self-hosted deployment exists, then run once:

```sh
sh scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs --self-test
SIMPLEOS_ARM64_ATTESTED_COMPILER=/absolute/path/to/simple \
SIMPLEOS_ARM64_COMPILER_RECEIPT=/absolute/path/to/compiler-receipt.env \
    sh scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs
```

2026-08-08 bounded status: the producer self-test passed its clean/seed/debug
and fabricated-stub rejection checks, while the single real producer invocation
rejected the canonical deployed compiler as `rust-seed-or-debug-forbidden`.
The shared root and the available current-origin worktree are dirty, so neither
can mint a frozen-source receipt. No ARM64 kernel, disk, manifest, QEMU launch,
or capture was produced by that attempt; do not retry until a new clean
current-origin worktree has a provenance-qualified self-hosted deployment.

Do not substitute `build/bootstrap/stage2`, `build/bootstrap/stage3`, or
`build/native_probe` merely because they are native ARM64 executables. The
available Stage 3 provenance is pinned to its original source root and does
not verify against the current shared root; it is historical diagnostic
evidence, not a transferable producer admission. A marker-only detector must
also not be relaxed to accept it without a current SHA-bound provenance check.

2026-08-08 clean-worktree check: `origin/main` resolved to
`e5617b6b1f22ec58df0f31250e2a5c7850279143`, but its fresh checkout contains
no deployed or Stage 3 compiler. An interrupted checkout is unusable and did
not start a build. The admission/launch row remains blocked until an external
bootstrap produces the current qualified compiler in a fully clean isolated
worktree.

### Q-NIL source mitigation (2026-08-01)

The Engine2D owner-helper consumers that returned `FontRenderer` through the
known aggregate ABI route were changed to initialize and read
`font_owner.active[0]` directly. This covers `fonts`, selected identity,
load/select paths, cache statistics, and `draw_text_bg`, matching the already
safe `draw_text` access. The focused source contract passes, but this is not
native or guest proof: the public `fonts() -> FontRenderer` return and its
external callers remain a separately tracked ABI boundary. Keep Q-NIL and
Q-FONT pending until the exact native regression can be built/run with a
current admitted compiler.

## 2026-08-04 ARM64-first convergence checkpoint

This checkpoint supersedes bootstrap, argv, and Clang migration work for this
lane. ARM64 WM/QEMU is the sole priority; the Clang-20 browser-demo lane remains
owned elsewhere and must not be edited or included in an ARM64 commit.

Integrated `origin/main` revision: `e35bdbbcbfdb`. It includes the strict-stub
producer/consumer stack and the later sibling WM/VMM changes, including
`177754a3ee` (WM QEMU gate fixes), `cb1d5d3260` (generational WM registry), and
`2915bba5ec` (4K TCG bring-up capacity/readiness). The clean integration
worktree had no unrelated changes after rebase.

Current fail-closed evidence, each checked once:

| Gate | Result | Meaning |
|---|---|---|
| Attested ARM64 producer | `canonical-pure-simple-compiler-unavailable` | No compiler+receipt pair satisfies native smoke, strict no-stub, no-fabrication, and measurement policy. |
| ARM64 QMP evidence consumer | `canonical-kernel-missing` | No canonical ELF/disk/manifest set exists; QEMU was not launched. |
| Process audit | No `qemu-system-aarch64` process | No stale or synthetic run can be mistaken for live evidence. |

Known candidates are inadmissible. `build/native_probe/simple` previously
reported 512 fabricated weak-zero stubs. Phase 2 and Phase 3 pure-Simple
artifacts reach LLVM translation but fail the focused non-entry module-global
probe with a nil-receiver runtime trap. None may be relabeled, copied, or given
a hand-written passing receipt.

### Remaining critical path

1. Receive a separately produced pure-Simple compiler plus receipt satisfying
   `simpleos-arm64-compiler-receipt-v1`. Compiler construction is an external
   dependency while bootstrap work is explicitly out of this lane.
2. Verify the receipt identity without rebuilding: exact absolute compiler
   path, SHA-256, one-line `--version`, `native_smoke_status=pass`,
   `stub_fallback=forbidden`, `fabricated_stub_status=none`, and
   `measurement_status=measured`.
3. In one clean isolated current-`origin/main` worktree, run the attested ARM64
   producer once with the two explicit environment variables. Reject the run
   if its captured build log contains `FABRICATED`, `FABRICATED-NEW`,
   `unmeasured`, `unbaselined`, or weak-zero markers.
4. Only after producer PASS, run the ARM64 QMP evidence consumer once. Retain
   the compiler receipt, build/frozen-source manifests, ELF/disk hashes,
   serial/QMP logs, and before/after framebuffer captures under one evidence
   root.
5. Only after diagnostic QMP PASS, launch the single visible Cocoa QEMU window
   for the physical-input interval. The project owner performs click, title-bar
   drag, `a`, Ctrl press, and Ctrl release; correlate each input with a later
   guest frame and then prove process cleanup.

The repair/build loop is capped at three cycles. A missing admitted compiler is
not a fix cycle and must not be polled indefinitely. Once a producer or QEMU
attempt fails, preserve its cache/log, repair only the first real failure, and
retry at most twice. After the third failed cycle, stop with the exact remaining
failure instead of widening runtime bundles, enabling stub fallback, launching
against stale artifacts, or rerunning an identical command.

## 2026-08-04 post-sync resume audit

GitHub `main` advanced through `e7ef812c11`, including the strict
module-global/stub-debt repair, ARM64 gate-trace scenarios, and the cross-platform
`sys_get_args` repair needed by later native probes. The rebase file-count guard
passed (110118 -> 110130 tracked files), and the two argv commits were pushed.

The newly added ARM64 SSpec was executed once with the user-authorized Rust seed
as diagnostic source-contract coverage. The seed identified itself correctly;
it is not compiler admission, SPipe release evidence, or permission to build the
guest with a seed. No assertion failure was printed before the direct runner
exited, but no pure-Simple authenticated PASS is claimed.

The filesystem still has no `simpleos-arm64-compiler-receipt-v1` receipt or
Stage 4 output. The separately owned Stage 4 process remains CPU-active and has
entered its 1030-file native driver phase; it was neither restarted nor waited
on. Existing Stage 2/3 hashes are unchanged from the prior failed focused
module-global admission, so that identical command was not rerun. No
`qemu-system-aarch64` process was launched. The next executable action remains
receipt validation followed by one attested producer invocation.

## 2026-08-04 external producer completion audit

The separately owned Stage 4 process has now ended. Its bounded command used a
7200-second timeout, the retained output ends at
`Driver start: inputs=1030 backend=cranelift mode=one-binary`, and
`stage4out/simple` does not exist. This establishes a failed producer handoff;
the absence of a terminal timeout line means timeout is an inference from the
bounded process disappearing at that phase, not a claimed compiler diagnostic.

No compiler receipt appeared anywhere under the owned build roots, GitHub main
is unchanged at `87ee4312bb`, and no `qemu-system-aarch64` process exists. The
Stage 2/3 artifacts and hashes are also unchanged, so their identical failed
admission was not rerun. The ARM64 producer, QMP consumer, and physical-input
interval therefore remain gated by the same missing receipt-qualified compiler.
Do not retry the two-hour Stage 4 command from this lane; resume only with a new
producer artifact or a separately reviewed compiler-production repair.

## 2026-08-04 Phase 2 owner-reset admission result

GitHub `main` supplied `039cad933a` (`fix(compiler): reset LLVM function state
through owner`). A separately owned clean rebuild from that revision emitted a
22 MiB AArch64 Mach-O Phase 2 compiler and advanced beyond Phase 2 bootstrap
sanity. Its measured identity is:

- version: `simple-bootstrap 1.0.0-beta`
- SHA-256: `30e9889950e6ed620fcaea51fcb1fb472be200679d4c8cb12bf633c339193b37`

The attestation wrapper's fail-closed self-test passed once on current main,
including Rust-seed/debug and fabricated-receipt rejection. The one canonical
strict module-global admission for the new compiler then exited with signal 11.
Its final trace advanced beyond the earlier nil-field boundary and stopped
after:

```text
[mir-to-llvm] function:start __simple_main
[mir-to-llvm] function:locals __simple_main
[mir-to-llvm] function:params __simple_main
```

This is not admissible native-smoke evidence, so no
`simpleos-arm64-compiler-receipt-v1` receipt was created. The three-cycle
compiler fix/verify cap is exhausted. Stage 3 may not be opportunistically
relabeled or checked as a fourth cycle, and the ARM64 producer, QMP consumer,
and visible Cocoa interval remain unlaunched. Resume in a fresh scoped compiler
lane only after repairing the post-parameter LLVM translation crash; then run
the module-global and native compiler admissions once before returning here.

## 2026-08-04 resumed owner-layout repair result

The user authorized a fresh bounded repair lane. Two additional owner-layout
repairs reached `main`: `22b04a7b46` reads `MirBody.return_ty` through its
owner, and `6471bf9a57` constructs the flattened bootstrap `MirBody` through
its owner. The wrapper rebuild exited 1 with an empty transcribed log, so the
final cycle ran the same strict seed-bootstrap native-build directly to retain
the actual result. It compiled 725 units with zero failures and emitted:

- version: `simple-bootstrap 1.0.0-beta`
- SHA-256: `fd5fd23fd4ce3321eedaf9c9d7a0c369ed351371de4f32e60a3a3f6a91e29d0e`

The shared worktree advanced from `22b04a7b46` to `6471bf9a57` while that
compiler was building, so its source identity is unstable and independently
inadmissible. Its one canonical strict module-global check also exited 132 at
the unchanged trace boundary:

```text
[mir-to-llvm] function:start __simple_main
[mir-to-llvm] function:locals __simple_main
[mir-to-llvm] function:params __simple_main
runtime error: field access on nil receiver
```

The fresh three-cycle cap is exhausted. No compiler receipt, ARM64 artifact
producer, QMP consumer, or Cocoa QEMU launch is permitted from this output.
The next lane must start from a stable `6471bf9a57` or later source snapshot
and diagnose the remaining post-parameter return-type conversion without
reusing this source-unstable candidate as evidence.

## 2026-08-10 rung-(d) minimum-path execution plan (from wm_capture_pipeline_gap research)

Source of truth: `doc/01_research/os/simpleos/wm_capture_pipeline_gap_2026-08-10.md`
(commit `a3b47107341`). This section turns that research into ordered,
execution-ready steps. Read the research doc in full before touching anything —
it carries the exact line numbers and the archived-log census this plan relies on.

### Corrected premise — the page fault is STILL OPEN

An earlier session recorded the `rt_string_concat`/`memcpy` page fault as
resolved. That claim is WRONG: the two newest archived runs
(`20260810T083128Z`, `20260810T112327Z`) carry an identical `rip=` distribution
(`3x 0x800434e`, `3x 0x8004350`, `1x 0x8004bc0`, `1x 0x8004bc2`) and wild
`cr2=0xffffffffffffff8e`. The "resolved" belief came from one clean-looking run
that had actually failed earlier for a different reason. Root cause is UNKNOWN —
only the symptom signature and the crash site region
(`_engine2d_draw_ir_render_glass_material`,
`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:508`, called from `:698`
within `_engine2d_draw_ir_render_commands` `:1420`) are known. Root-cause
investigation is a SEPARATE, HARDER track (Track W2 below); the minimum path to
rung (d) deliberately does not depend on it.

### Track W1 — chrome-only first frame to rung (d) [minimum path]

Scope IN: gate `runtime_content_frames` behind a guest flag so the first frame
skips the crashing content-frame paint; readiness fires; host-side capture runs;
non-uniform baseline PPM produced. Scope OUT (explicitly deferred): fixing the
fault itself; F11 maximize/restore and browser-event PPM comparisons (they will
still fail without content painting — expected and correct); any change to
`check-simpleos-wm-fullscreen-evidence.shs` checks.

Dependency note: this track needs NO paint output at all. With the flag off,
`render_baremetal_frame` yields an empty `[WmContentFrame]`; every window takes
the already-tolerated degraded branch (`engine2d_wm_frame_executor.spl:277-287`,
`renderable_images == 0`, coverage check passes) and the frame composites WM
chrome only (background, three window frames + titlebars, taskbar) — more than
enough for a non-uniform PPM. Therefore Track W1 is fully INDEPENDENT of the
blink paint-pipeline lane (`doc/03_plan/lib/browser/blink_style_paint_plan_2026-08-10.md`);
the two can proceed in parallel.

Precondition (MANDATORY, from the research doc's implementer trap): sync the
build tree to origin/main and blob-verify
`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs` contains
`deep_fields: &[crate::mir::AggregateFieldCopy]` before building any kernel.
The local checkout was 46 lines behind origin on that file; building without the
struct deep-copy fix will mis-attribute results.

Ordered steps:

1. `src/os/desktop/shell.spl` — add module-level
   `val _WM_CONTENT_FRAMES_ENABLED: bool = false` next to `_WM_TRACE`
   (`shell.spl:99`), preferably read from the generated config
   `build/os/generated/generated/simpleos_log_config.spl` (written by the gate
   at `check-simpleos-wm-fullscreen-evidence.shs:936`) so it flips without a
   source edit. Acceptance: flag exists, default off in production, lint clean.
2. `src/os/desktop/shell.spl:990` (`render_baremetal_frame`, `:971-998`) —
   guard `val content_frames = self.runtime_content_frames(scene_revision)`
   to yield an empty `[WmContentFrame]` when the flag is off. Do NOT touch
   `runtime_content_frames` itself (`shell.spl:1295`) or the executor.
   Acceptance: with flag off, executor logs
   `[wm-frame] window-degraded ... (x3)` and `first_frame_revision > 0`.
   Confirm `host_gpu_required` stays false (`gui_entry_desktop.spl:581` passes
   `backend_required: false`) — do not change it.
3. Flip `_WM_TRACE` to `true` for the diagnostic run (`shell.spl:99`, executor
   receipts at `engine2d_wm_frame_executor.spl:250-282`). This is the highest
   observability win: `[wm-render-step] at=...` names the step where any future
   hang occurs. Acceptance: receipts visible in serial log of the diagnostic run.
4. Run the gate lane. Acceptance oracle (exact expected log, per research §5):
   `[desktop-gui] first-frame-rendered scene_revision=N` (N>0) →
   `[engine2d-simd] ...` → font evidence → `[desktop-gui] desktop-ready` →
   `[production-readiness] ...`; host side:
   `simpleos_wm_fullscreen_scanout_capture_size=33177600` and four PPMs of
   `24883215` bytes each, with `baseline.ppm` NON-UNIFORM.
5. Only if step 4 does not produce a non-uniform PPM: add the belt-and-braces
   solid fill + one contrasting rect via `FramebufferDriver`
   (`gui_entry_desktop.spl:424`, between `:428` and `:429`). It proves less;
   skip it if step 4 succeeds.
6. Update `doc/08_tracking/bug/freestanding_text_local_recompare_flips_material_admission_2026-08-10.md`
   § Layer 3 (OPEN) to record the fault persists as of run `20260810T112327Z`,
   and report the flag run as a DIAGNOSTIC run, not a gate pass.

Hard constraints (do not weaken):
- `wm_content_frame_web_provenance_valid` and every check in
  `check-simpleos-wm-fullscreen-evidence.shs` stay untouched. The flag lives in
  the guest and is off by default.
- Next hard gate after the frame: `[engine2d-simd] fatal ... zero-runtime-receipt`
  (`gui_entry_desktop.spl:597-600`) hard-exits if the SIMD fill never ran; a
  chrome-only frame still fills large regions so this should pass — verify, don't assume.

Measurement traps carried forward:
- Read ALL archived runs under
  `build/simpleos_wm_fullscreen_evidence/runs/<ts>/`, not just the newest; the
  `provlane` runs have NO serial.log — do not use them. `stat -c %y` each
  `serial.log` — archived logs can predate their directory stamp.
- Use `/usr/bin/grep` for anything under `build/` — the wrapped ugrep honours
  `.gitignore` and sees nothing there.
- Record binary identity (`readlink -f bin/simple` + stat) with every timing/run.

### Track W2 — root-cause the memcpy/rt_string_concat fault [separate, harder]

UNKNOWN root cause; known only: fault signature above, crash region in
`_engine2d_draw_ir_render_glass_material` /
`engine2d_draw_ir_glass_material_pixels`, `cr2` a small negative offset off a
null-ish base (length/index computed as -1 used unsigned, or a struct
field-index collision — same class as Layer 2 in the bug doc). Do not assume a
diagnosis. Entry aids: `_WM_TRACE` receipts from W1 step 3; the per-pass
allocation profile (three content-frame passes, ~2 MiB style buffers + 3x 8 MiB
`array-repeat` pixel buffers on a never-freeing bump heap — an OOM-into-wild-
pointer hypothesis is plausible but UNVERIFIED). Tracking anchor stays the
Layer 3 section of the bug doc. This track gates full acceptance (content
frames, F11/browser PPM comparisons) but NOT rung (d).

### Cross-track prioritization (2026-08-10, three research tracks)

Order recommendation given tonight's spend-cap pressure:
1. **Blink `style_paint` lane** (`doc/03_plan/lib/browser/blink_style_paint_plan_2026-08-10.md`)
   — cheapest and fastest to a REAL green result: two new files, one unit spec,
   no build, no QEMU, no host contention. Do first.
2. **WM Track W1 chrome-only rung (d)** (this section) — highest value (unblocks
   the whole capture pipeline and proves scanout+compositor+capture end to end)
   at moderate cost: a small guest edit plus one gate run; the main cost is the
   kernel rebuild + QEMU cycle, and the origin-sync precondition.
3. **K26 board synthesis** (`doc/03_plan/hardware/riscv/k26_rv32_ddr_bitstream_bringup_plan_2026-08-10.md`)
   — highest multi-hour-stall risk (30–90 min Vivado, ≥30 GB RAM, collides with
   any concurrent `native-build`). Run only in a quiet host window; defer
   rather than override guardrails.
Do NOT start WM Track W2 (fault root-cause) tonight — unknown root cause,
open-ended cost; it gates full acceptance but not rung (d).
All three tracks are code-independent; blink and W1 can run in parallel; the
board track shares only host resources.

## 2026-08-21 ARM64 `Color` resume handoff

The old `Color.rgb` crash was refined to ambiguous production type ownership,
not a still-universal small-struct return failure.  Framebuffer consumers now
use the explicit `FbColor` import alias.  An admitted Stage-2 compiler proved
the duplicate-name fixture, the adjacent aggregate-return class, and the real
`os.compositor.decorations` path with exact channel values.

Current host readiness is PASS: macOS arm64, HVF, QEMU `virt`, and `ramfb`.
The canonical attested producer stops before building with
`canonical-pure-simple-compiler-unavailable`; Stage 2 intentionally exposes
only `compile` and `native-build`, while the producer requires a provenance-
accepted full CLI with `os build`.

Resume without repeating the failed direct kernel diagnostic:

1. Provide a current provenance-qualified full pure-Simple CLI accepted by
   `scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs`.
2. From the clean `dd4c-qemu` workspace, run that producer once and retain its
   build and frozen-source manifests.
3. Run `scripts/check/check-simpleos-arm64-qmp-input-evidence.shs` once.  Require
   `desktop-ready`, nonblank device-origin RAMFB capture, correlated real QMP
   input, and the unchanged 2D/Web/GUI/WM assertions.

Owner: ARM64 SimpleOS QEMU rendering lane. Merge owner and final reviewer:
normal/highest-capability Codex. No generated manual or done mark is accepted
until the live QEMU receipt exists.
