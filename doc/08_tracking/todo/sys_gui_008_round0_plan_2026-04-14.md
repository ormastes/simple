# SYS-GUI-008 virtio-gpu QEMU Baseline — Round-0 Plan (2026-04-14)

**Ticket:** `sys-gui-008` (Row 4 of
`doc/03_plan/gui_drawing_layer_variations.md`) · **Status:** Round-0
(planning + scaffold only — NOT In-Progress) · **Owner:** GUI stack WG

This Round-0 plan scopes the virtio-gpu accelerated path baseline in QEMU
(V1 variation). It establishes the gates, acceptance criteria, round
rollout, and dependency preconditions so a subsequent implementation
agent can land the actual QEMU framebuffer capture and baseline PPM.

Round-0 lands:
1. This plan doc.
2. A scaffold spec at `test/system/sys_gui_008_virtio_gpu_baseline_spec.spl`
   with a single failing `it{}` documenting the acceptance sequence
   (no runtime work — placeholder only).
3. Row 4 status move in
   `doc/03_plan/gui_drawing_layer_variations.md` from `Blocked` to
   `Round-0 plan landed` with a link to this file.

Round-0 deliberately does NOT modify compiler, runtime, or production
OS code. The existing tracker at
`doc/08_tracking/todo/sys_gui_008_virtio_gpu_qemu.md` remains the
long-form acceptance record and is referenced here, not rewritten.

---

## 1. Scope

Baseline virtio-gpu render capture via QEMU. Goal: prove the
`GpuCompositorBackend` over `backend_virtio_gpu` renders the same bare
desktop scene as sys-gui-006's framebuffer lane, captured headless
under `-display none` and diffed at ≤1% perceptual drift.

In-scope for the full SYS-GUI-008 rollout (Rounds 1-3 below):
- Reach `[desktop-e2e] desktop-ready` under scenario `x64-gpu-2d`.
- Capture the scanout to PPM via QMP screendump (or
  `VirtioGpuDriver.dump_scanout()` / `read_pixels`).
- Commit a baseline at
  `test/baselines/simpleos_desktop_virtio_gpu/desktop_scene.ppm`.
- Pass `test/system/sys_gui_008_virtio_gpu_baseline_spec.spl`
  in prerun + live lanes, diffing against the sys-gui-006 PPM
  under `profile_wm_default`.

Out-of-scope (explicitly deferred):
- `wm_compare` third-lane integration (Round 4 of the long-form tracker).
- Headless CI lock and RSS budget (Round 5 of the long-form tracker).
- Any work touching `src/runtime/hosted/`, `src/app/ui.chromium*`,
  `src/app/ui.electron/`, or `src/compiler_rust/`.

---

## 2. Gates

Round-0 → Round-1 gate:
- **Gate 0a** — sys-gui-006 bare-desktop LIVE-GREEN confirmed.
  As of 2026-04-14 (per
  `doc/08_tracking/todo/sys_gui_006_round10_status_2026-04-14.md`),
  Blocker 1 is cleared by commit `e516e2a0f484`; Blocker 2
  (`launcher:fail registered=0` before `desktop-ready`) remains open
  and gates Round-11. Round-1 of sys-gui-008 **must not** begin until
  `doc/08_tracking/todo/sys_gui_006_bare_desktop_resume_2026-04-14.md`
  is marked LIVE-PROVEN with `desktop_scene.ppm` committed.
- **Gate 0b** — Scaffold spec compiles clean under
  `bin/simple lint test/system/sys_gui_008_virtio_gpu_baseline_spec.spl`.

Downstream gates (claimed per round):
- **Gate 1** — Entry spec compiles and `gui_entry_engine2d_virtio.spl`
  reaches `[desktop-e2e] desktop-ready` on scenario `x64-gpu-2d`.
- **Gate 2** — QEMU boots under `-display none` with virtio-gpu
  scanout readback; framebuffer capture emits a non-zero PPM.
- **Gate 3** — Baseline PPM committed at
  `test/baselines/simpleos_desktop_virtio_gpu/desktop_scene.ppm`
  and spec self-compares ≥95% under `profile_wm_default`.
- **Gate 4** — Cross-baseline diff vs.
  `simpleos_desktop_framebuffer/desktop_scene.ppm` ≤1% perceptual.

---

## 3. Acceptance Criteria

Mirrors the long-form tracker's "Acceptance criteria" section. The
SYS-GUI-008 ticket is accepted when all of the following hold:

- `test/system/sys_gui_008_virtio_gpu_baseline_spec.spl` passes in
  prerun and live lanes.
- Scene diff vs. `simpleos_desktop_framebuffer/desktop_scene.ppm`
  ≤1% perceptual pixels changed.
- `gui_entry_engine2d_virtio.spl` emits `[desktop-e2e] desktop-ready`
  under scenario `x64-gpu-2d`.
- `VirtioGpuBackend.name()` returns `"virtio-gpu"` at the runtime
  assert gate (already true at L76 — must stay).
- Spec hard-fails if `[desktop-ready]` marker missing
  (regression gate mirrors sys-gui-006's contract — no green-washing).
- Scenario runs under `-display none` with scanout readback; wall
  clock ≤ framebuffer lane + 50%.
- No stray `unreachable!` or `TODO` introduced in
  `backend_virtio_gpu.spl`, `display_backend.spl`, or the entry.

Round-0 itself is accepted when:
1. This plan doc lands.
2. Scaffold spec compiles clean (`bin/simple lint` green).
3. Row 4 status updated to `Round-0 plan landed`.

---

## 4. Dependencies

- **sys-gui-006 bare desktop — LIVE-GREEN (HARD BLOCKER)**.
  Reference scene for the diff. As of 2026-04-14 Round-10, Blocker 1
  cleared (commit `e516e2a0f484`); **Blocker 2 still open** —
  Round-11 has NOT yet confirmed LIVE-GREEN. Round-1 of sys-gui-008
  is gated on Round-11 confirmation. See
  `doc/08_tracking/todo/sys_gui_006_round10_status_2026-04-14.md`.
- **sys-gui-006 with-apps** — should also land green
  (`doc/08_tracking/todo/sys_gui_006_with_apps_resume_2026-04-14.md`)
  so the multi-window scene exercises the compositor, not just a
  flood-fill. Soft dependency; not a hard blocker for Round-1.
- **sys-gui-007 (disk lane)** — NOT a blocker. Independent lane.
- **`gui_layer_contract.md` Row 1** — already locked upstream. No work.
- **Compiler blockers from sys-gui-006 Round 8** — cleared by
  commits `e516` (GLOBAL_ENUMS fallback) and `f940` (MIR method call
  qualification).

---

## 5. 3-Round Rollout

Round-1 through Round-3 correspond to the "implementation" arc. The
long-form tracker Rounds 0-5 remain the source of truth for the full
rollout; this plan specifies the three rounds needed to reach a
committed PPM baseline (i.e. the minimum viable SYS-GUI-008 exit).

### Round-1 — Entry spec + compile
**Precondition:** Gate 0a (sys-gui-006 Round-11 LIVE-GREEN) + Gate 0b
(scaffold lints clean).

- Extend `examples/simple_os/arch/x86_64/gui_entry_engine2d_virtio.spl`:
  construct `GpuCompositorBackend.new(gpu)`, install as compositor
  backend, reach `[desktop-e2e] desktop-ready` on a blank scene.
- Replace the Round-0 scaffold's placeholder `it{}` body with the
  real `build_os` + `spawn_guest_with_qmp` + `wait_for_serial_marker`
  sequence, modelled on
  `test/system/simpleos_desktop_framebuffer_spec.spl` L170-220.
- **Gate 1 artifact:** scenario `x64-gpu-2d` boot log containing
  `[desktop-e2e] desktop-ready`, captured at
  `build/os/sys_gui_008_virtio_qemu_serial.log`.

### Round-2 — QEMU boot + framebuffer capture
**Precondition:** Gate 1.

- Wire `capture_qemu_vm` (QMP screendump) into the spec's live
  lane. If QMP screendump of the virtio-gpu scanout returns an
  empty/placeholder surface, fall back to a guest-side
  `VirtioGpuDriver.dump_scanout()` or `read_pixels` path and
  marshal the buffer to host.
- Run under `-display none` to prove headless capture works.
- **Gate 2 artifact:** non-zero
  `build/os/sys_gui_008_virtio_capture.ppm` produced by a live run.

### Round-3 — PPM baseline + parity diff
**Precondition:** Gate 2.

- Commit baseline at
  `test/baselines/simpleos_desktop_virtio_gpu/desktop_scene.ppm`
  via `UPDATE_BASELINE=1 bin/simple test ...` — first-run
  self-heal path.
- Wire the spec to diff against
  `test/baselines/simpleos_desktop_framebuffer/desktop_scene.ppm`
  at ≤1% perceptual drift using the same Row 8 diff harness.
- Two fresh recordings must each score ≥95% against the committed
  baseline under `profile_wm_default` (determinism proof, not
  self-identity).
- **Gate 3+4 artifact:** green
  `test/system/sys_gui_008_virtio_gpu_baseline_spec.spl` prerun
  + live; baseline PPM committed.

Rounds-4 and -5 (wm_compare third lane + headless CI lock) are
tracked separately on the long-form tracker and are NOT part of
this three-round exit.

---

## 6. Scaffold Artifact

`test/system/sys_gui_008_virtio_gpu_baseline_spec.spl` — a single
failing `it{}` that documents the acceptance sequence. Body uses
`expect(false).to_equal(true)` as a placeholder fail so the suite
does not accidentally green-wash; the implementation agent replaces
the body in Round-1.

---

## 7. Guardrails (copied for the implementation agent)

- Never convert a failing `expect(false)` into a skip/xfail to get
  the suite green. The sys-gui-006 Round-9 triage forbids it.
- Never skip the `wait_for_serial_marker` — dropping the
  `[desktop-ready]` marker wait is green-washing and violates the
  acceptance contract.
- Never touch `src/runtime/hosted/`, `src/app/ui.chromium*`,
  `src/app/ui.electron/`, or `src/compiler_rust/`.
- Implementation must stay in `.spl`/`.shs` per `CLAUDE.md`.

---

## Cross-references

- Long-form tracker:
  `doc/08_tracking/todo/sys_gui_008_virtio_gpu_qemu.md`
- Row 4 source: `doc/03_plan/gui_drawing_layer_variations.md`
- sys-gui-006 gating status:
  `doc/08_tracking/todo/sys_gui_006_round10_status_2026-04-14.md`
- sys-gui-006 bare-desktop resume:
  `doc/08_tracking/todo/sys_gui_006_bare_desktop_resume_2026-04-14.md`
- Template spec:
  `test/system/simpleos_desktop_framebuffer_spec.spl`
- Existing virtio backend:
  `src/lib/gc_async_mut/gpu/engine2d/backend_virtio_gpu.spl`
- Existing compositor backend:
  `src/os/compositor/display_backend.spl`
- Existing entry: `examples/simple_os/arch/x86_64/gui_entry_engine2d_virtio.spl`
