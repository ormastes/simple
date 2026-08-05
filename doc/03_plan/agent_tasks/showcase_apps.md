# Showcase apps agent tasks

- 2D sidecar: inventory primitives and dummy paths; propose Engine2D/readback coverage. Completed read-only and reviewed by root.
- Web sidecar: inventory HTML/CSS and browser/WM gaps; propose standards page and interaction checks. Completed read-only and reviewed by root.
- GUI/integration sidecar: inventory catalog, SimpleOS, docs, skills, and manuals. Completed read-only and reviewed by root.
- Merge owner: root agent.
- Final reviewer: root/highest available model; broad findings and exclusions require direct source/test evidence.

Concurrent compositor files remain owned by another active lane. Integration proceeds through clean catalog/app/docs/tests first and merges compositor changes only after ownership is clear.

## Status (2026-07-15) — verified surface × app matrix

| App | Standalone | Host-WM | SimpleOS WM |
|-----|-----------|---------|-------------|
| 2D showcase | ✅ 320×240 anti-fake gate passes (720p interpreter-timeout) | ✅ `wm_2d_child.ppm` 1473 colors, 99.998% nonzero | ⛔ blocked (compiler bug, see below) |
| Widget/GUI showcase | ✅ `widget_showcase_720p.ppm` 15-color vector UI | ✅ `wm_widget_child.ppm` live widget state | ⛔ blocked (compiler bug) |
| Web browser showcase | ✅ CSS/layout/paint engine proven `realeng_640.ppm` 8 source-matching colors; full-text render toolchain-gated | — | ⛔ blocked (compiler bug) |

**Verified: 5 surface cells** with real pixels. Dummy-impl audit done (3 fakes filed). Docs/guide/spipe skill updated + pushed.

### SimpleOS WM surface — 6 blockers cleared, 7th root-caused
Boot advanced from crash → boots fully through pmm/vmm/vfs/framebuffer/4K-scanout/engine2d/input/compositor/shell-init → **reaches the paint call**. Fixes landed: O(n²) framebuffer alloc (`1fe2653d`), compositor native-build (`3e5ef0c9`), font-load degrade guard (`c0f5d02f`), two spawn `Option`-nil miscompiles (`e8c4c3b1`/`f09dadd6`, faults 165→2), baremetal mutex halt (`ff302353`), executor scalar-dim workaround (`05102c73`).

**Remaining blocker:** native-build cross-module **field-resolution** bug — a systemic name-keyed heuristic collision in the type-inference-less native path (`resolve_field_index`, function_lowering.spl:582) that shifts cross-module class-field reads by one slot. Confirmed across the whole spawn+render graph (`FramebufferDriver.width`→garbage 34.8M, `TaskbarModel.revision`→garbage, kernel spawn-loader fields→garbage), so per-site app-level workarounds are unbounded whack-a-mole. Array-slot hypothesis **disproven** (minimal repro resolves correctly on the exact live target). Bug doc `simpleos_native_build_framebufferdriver_crossmodule_field_offset_shift_2026-07-14.md` has a drop-in `[FIDX]` diagnostic + one-compile pin procedure.

**Compiler-rebuild wall (fully diagnosed 2026-07-16):** the root fix needs a rebuilt compiler, but this Mac **cannot self-host-rebuild** it — not a link-flag issue but the known-critical IN_PROGRESS bug `bootstrap_stage2_empty_mir_bodies_2026-07-05` (Stage-2 MIR→LLVM lowering unfinished + missing runtime symbols `_rt_volatile_write_u64`/`_val_kind` on aarch64-apple-darwin). Correct bootstrap cmd = `scripts/bootstrap/bootstrap-from-scratch.sh` (NOT `bin/simple build bootstrap`, which uses the stale deployed binary). The seed lacks `--features llvm`, so use `--backend=cranelift`.

### Decision (2026-07-16): accept 5/9, hand off SimpleOS surface
Per user direction, the deliverable is the **5 verified cells** (2D + widget standalone/host-WM real PPMs; web CSS engine proven) plus the complete SimpleOS diagnosis, filed bug, and 6 landed fixes (all integrated by the peer's active OS/gui render lane, e.g. `4c1a5365` "pinned Engine2D optional fields"). The **4 SimpleOS cells** are handed off to: (a) the peer session actively driving the render workarounds, and (b) the ready Linux-host `[FIDX]` pin+fix procedure for the compiler root fix. No further SimpleOS edits from this lane (avoid colliding with the peer's active render files).

## WM showcase lane (docs written 2026-08-05 — code owned by a parallel lane)

A parallel lane is building the **WM showcase**: the GUI, web, and 2D showcase
windows managed together by a window manager, plus a **taskbar derived from live
window state**, with the result verified by screen capture. This section records
the **intended contract** and what is verifiably in the tree today. **This lane
did not write the code and does not attest it works.** Every row below is
labelled by its evidence level; nothing here is a shipping claim.

### What is in the tree today (verified 2026-08-05, all paths read)

| piece | file | state |
|---|---|---|
| Taskbar schema | `src/lib/common/ui/taskbar_model.spl` | **Present, schema-only.** `AppRef`, `WindowRef` (carries `minimized: bool`), `TrayItem`, `TaskbarLaunchError`, `TaskbarModel{pinned,running,tray}`, `empty_taskbar_model()`. It contains **no derivation function** — do not cite it as the live-derivation site. |
| Live derivation | `src/app/ui.web/taskbar_shell.spl:55` | **Present.** `build_taskbar_model(registry: UiWindowSurfaceRegistry, pinned: [AppRef], tray: [TrayItem]) -> TaskbarModel` materialises `running` by iterating `registry.bindings`, so the running list **is** live window state. `pinned` and `tray` are caller-supplied, not derived. Sibling `build_taskbar_model_with_minimized(...)` at `:82` takes explicit `minimized_surface_ids`. |
| Session entry point | `src/app/ui.web/_HostTaskbarRuntime/host_taskbar_runtime.spl:144` | **Present.** `host_taskbar_runtime_taskbar_model(session: UISession)` feeds `session.window_surfaces` into the derivation above. |
| Pin persistence wire | `src/lib/common/ui/taskbar_pin_wire.spl` | **Present, codec only.** `SIMPLE_TASKBAR_PINS_V1` header plus line encode/decode and field validation. It performs **no storage** — persistence is the runtime's job. |
| Window lifecycle | `src/lib/common/ui/wm_window_state.spl` | **Present.** Scalar i32 FSM: `NORMAL/MINIMIZED/MAXIMIZED/CLOSING/CLOSED` with `..._minimize / _maximize / _restore / _begin_close / _finish_close / _accepts_input`. No registry, no window list. |
| Multi-surface demo tree | `src/lib/common/ui/wm_full_stack_demo.spl` | **Present, a demo widget tree — not a WM.** One `wm_full_stack_demo_tree(...)` embedding a 2D surface (handle 101) and a web surface (handle 102). |
| Showcase catalog | `src/lib/common/ui/showcase_catalog.spl` | **Present, and reports NOTHING ready** — see the correction below. |
| Capture evidence | `src/os/compositor/hosted_wm_capture_evidence.spl`, `wm_gui_window_drawing_evidence.spl`, `qemu_capture.spl`, `screenshot_compare.spl` | **Present.** Contract detail in `doc/05_design/showcase_apps.md`. |

### NOT in the tree — do not document these as shipped

- **No unified WM-showcase driver module.** The pieces live in three trees
  (`src/lib/common/ui`, `src/app/ui.web`, `src/os/compositor`); nothing ties
  catalog + taskbar + capture into one entry point.
- **No commit subject names a WM-showcase milestone.** The nearest landed work
  is `77c06285a7c` (`fix(wm): restore running pinned applications`),
  `11f6b9d75a6` (`fix(wm): keep lifecycle and input targets truthful`) and
  `9f229135544` (`fix(wm): advance native GUI routing gate`).
- **Hardcoded taskbars still exist** and are not live-derived:
  `src/os/desktop/modern_wm_readiness.spl:606` (`_readiness_taskbar_model`) and
  `src/app/wm_compare/production_gui_window_taskbar_widget_shells.spl:148`.
  A "taskbar derived from live window state" claim must name
  `build_taskbar_model` / `host_taskbar_runtime_taskbar_model` as the path
  actually taken, not merely that a `TaskbarModel` was rendered.

### Correction: the catalog attests ZERO ready surfaces

The 2026-07-15 matrix above marks five cells ✅. That is **capture-lane
evidence from that date**, not catalog readiness, and the two disagree:

- All nine readiness bits in `src/lib/common/ui/showcase_catalog.spl` are
  hardcoded `false` (lines 37-39, 47-49, 57-59), and `showcase_surface_supported`
  (`:70`) returns them directly.
- `test/01_unit/lib/common/ui/showcase_catalog_spec.spl:55` — *"reports only
  currently implemented launch surfaces"* — **asserts all nine are `false`**
  (lines 60-68). Flipping any bit to `true` is a spec-visible change.
- The PPM artifacts the ✅ rows cite (`wm_2d_child.ppm`, `wm_widget_child.ppm`,
  `widget_showcase_720p.ppm`, `realeng_640.ppm`) are **not present in the
  worktree** — they were transient build outputs. The rows are therefore a
  historical record, **not currently re-verifiable**, and must not be restated
  as present-tense status.

Neither statement is deleted here: the matrix records what a capture run
produced on 2026-07-15; the catalog records what the product currently declares
launchable. **When the WM showcase lands, the catalog bits and that spec are the
place the readiness claim must be made** — a green capture alone does not make a
surface "ready".

### Measurement rules for this lane

Capture-verified means a real readback with an absolute oracle, per
`.claude/skills/spipe.md` §"Equality is not correctness". Additionally:

- Read `Results: N total, M passed, K failed` (from `bin/simple test`) or the
  per-file `SPEC FILE VERDICT: … executed=N …` line. `bin/simple run` prints a
  **different** grammar (`N examples, M failures`, ANSI-wrapped) — the two
  patterns do not match each other's output.
- Never `tail -1` a spec log; never treat exit 0 as a pass (an unresolved `use`
  is only a WARN). Exit 143/255 with no output is a kill/timeout, not a result.
- Compare **executed example counts** between runs, not just failures — a
  module-load failure drops whole `describe` blocks at exit 0.
- Full trap list: `.claude/skills/spipe.md` §"Reading the verdict — how a spec
  run lies to you".

### Toolchain-gated (not app logic)
Web full-text glyph render: seed can't JIT the 17MB font sfnt path; deployed binary blocked by `rt_cli_arg_count`. Needs seed HIR fix or Stage-4 redeploy.
