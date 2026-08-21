# Feature: SimpleOS Screens + Render Lane Runnable & Hardened

## Raw Request
> make deep research and plan with agents, simple os to have configs, 2d rendering
> screen, web rendering screen, gui rendering screen, and existing default wm screen.
> in 2d showcase check events/click/drag/keytype, panel with scrollbar, linked panels,
> windows and widget (toolbar) on wm. web render showcase internal window widget,
> scrollpane and bar, similar to gui and wm. check only depends render land and
> dedicated host interface, and use almost all same logic and code except HAL.
> check simple keyboard mouse driver and HAL layer connected to simple 2d. vulkan
> driver on simple os. and optimize simple 2d SIMD backed (config detail simd) — it
> is too slow, analyze and optimize, check buffer and other optimization is not
> applied, research 2d optimizations and apply. make research, update design and
> detail parallel plan; detail so mostly sonnet can do, assign difficult to opus.
>
> Follow-up: `$sp_dev` — complete wm and render lane SimpleOS-runnable and harden
> plan. complete the detail plans in parallel agents.

## Task Type
feature

## Refined Goal
Make the WM/GUI/Web/2D render lane selectable and runnable on SimpleOS via boot
config, unify the four screen targets on one `DrawIrV3Scene` render contract plus a
single `ScreenHost` HAL, connect real keyboard/mouse input through an IRQ-backed HAL
path into simple-2d, remove the measured 2D slowness at its root (in-place SIMD
kernels, damage-driven present, backing stores, glyph atlas), and phase a real
Vulkan (Venus/virtio-gpu 3D) driver — with fail-closed evidence at every hop.

## Status: IMPLEMENTING — first slice landed 2026-08-06

### Landed this slice
- **WS-A**: `rc_conf_value()` + `screen_type/_res/_simd` normalizers (no Dict —
  4-entry array scan); `backend_factory.spl` with pure
  `resolve_screen_type(requested, profile)` + `match` registry; `boot_runtime_profile()`
  from a real PCI class-0x03 probe. Specs 12/12 and 14/14, negative control 13/14.
  **Plan bug caught**: the plan's A3 would have produced a BLANK SCREEN — branching on
  `requested=="wm"` skipped `bga_init_framebuffer` for any fallback or gui/web
  selection. BGA init is now unconditional.
  *Flag*: `init_services.spl` is now the FIRST `src/os/kernel/**` → `src/os/compositor/**`
  import in the tree (limited to the pure half); splitting `backend_factory` into
  pure-selection + constructor modules would remove the edge.
- **WS-B**: `ScreenHost` (additive, `screen_host.spl:32`) + `HostInputEvent`
  (`Pointer{x,y,button,pressed,wheel}` / `Key{code,ch,down,mods}`; `button`/`mods` are
  `i64` to dodge enum-payload defects; wheel positive = scrolls down) + `showcase_core`.
- **WS-E**: feature bits 0–4, capset opcodes, 3D/blob opcodes, `virtio_gpu_capset.spl`;
  modern path now ACKs `VIRGL|BLOB|CONTEXT_INIT` instead of writing 0. 46/46 + 11/11
  2D regression; sabotage check 41→36. **Removed its own fabricated
  `VIRTIO_GPU_CAPSET_VENUS = 4`** — Venus is located by enumeration, never a guessed id.
  **Fixed a real OOB DMA hazard**: `gpu_get_capset` submitted an unbounded
  `24 + max_size` device-writable descriptor against a fixed 4096-byte buffer; now
  rejects rather than truncates.
- **Key-code vocabulary**: adopted (not invented) Windows VK / W3C `keyCode`, already
  latent in three places. `key_code.spl` + 17/17 spec comparing all four producers
  against absolute integers, mutation-proven (16/17 when SDL LEFT/RIGHT swapped).
- **Guards**: Vulkan bridge device allow-list; `check-ui-showcase-layering.shs`
  (fail-closed, selftest fatal, no off-switch).

### WS-D — measured, and it moved the numbers
640px span × 400 iters, n=10, 11 fresh processes (run 1 discarded — the enable check
memoizes): **blend p50 63 → 27 ms**, **fill 8 → 0 ms**, max RSS 42.5 → 34.8 MB,
`PARITY_DIFFS` **210 → 0**.
- **Correctness bug fixed, not just perf**: `_scalar_blend_row` was producing WRONG
  PIXELS — `val d = dst[idx]` off an `any` receiver then `(d >> 24)` yielded garbage
  (da=17 read as 138). Fixed with `as u32`.
- `SIMPLE_2D_SIMD=auto|off|sse2|avx2|neon` allow-list added; default now scalar.
- **PROVENANCE ALERT — invalidates a standing assumption**: `readlink -f bin/simple`
  → `bin/release/x86_64-unknown-linux-gnu/simple`, md5 `ed53cc5f255e269ca27c4cd83b17aef9`,
  57 MB, and it **emits the Rust-seed banner**. All numbers above are JIT-over-Cranelift
  with C externs — **NOT self-hosted native**. Any AC-7 claim of "deployed native
  binary" is currently unmet by the tooling itself.
- Filed: `any_receiver_element_read_shift_and_tag_2026-08-06.md` (compiler: three read
  forms, three results, one turning an int shift into a float),
  `engine2d_simd_span_kernels_slower_and_fill_colour_corrupt_2026-08-06.md`
  (existing `rt_engine2d_simd_fill_span_u32` is slower AND wrong:
  `0xFF112233`→`0xFF132233`), report `doc/09_report/ws_d_2d_perf_d0_d2_2026-08-06.md`.
- D2's C half is **filed, not merged** — it needs rebuilding/redeploying the shared
  `bin/simple`, refused mid-session with other agents live.
- **SimpleOS/QEMU SIMD: unmeasured.** The C blend kernel is reachable and numerically
  correct on x86_64 host under JIT; there is no evidence either way on target.

## Blockers — AFTER adversarial verification (`screens/ws_blocker_verification.md`)
Five planning-agent claims were independently re-checked against source. Two were
overstated; the verified severities are below. Do not implement against the
pre-verification wording.

1. **PARTIALLY TRUE — AC-9 bridge gate only.** `check_simpleos_multiconfig_live_evidence.spl:145`
   does hard-equal the legacy `disable-modern=on` device, and no `venus=on` exists
   anywhere in `scripts/` or `src/`. But it is reached only by
   `derived_engine2d_vulkan_bridge_status` (:138); the primary
   `derived_engine2d_vulkan_status` (:117) never consults the device string. Scope
   the fix to the *bridge* AC — the earlier "every Vulkan claim is false" framing
   was wrong. Fix must still *tighten* (block a Vulkan claim asserted on the 2D
   device), never loosen.
2. **REFUTED — keytype-on-WM is NOT blocked.** `wm_fs_key_event` (:241) already
   ships keycodes across the WM boundary as `kind="key"` + `button=keycode`, and the
   encoder/decoder round-trips `button`. Residual gap is narrower: no character,
   modifier, or wheel encoding. Downgrade from blocker to a small encoding task on B1.
3. **PARTIALLY TRUE — and both numbers were wrong.** `common.ui.backend_factory`
   genuinely does not exist, but there are **four** importers, not seven (three
   further files only mention it in `@cover` comments — the likely miscount source).
   The fail-open claim is **empirically refuted**: running `container_detect_spec.spl`
   yields `error: test-runner: no examples executed` / `1 total, 0 passed, 1 failed`.
   They fail loudly. Still worth fixing, but they are not silent false coverage.
4. **CONFIRMED — AC-4 needs a schema change first.** `ShowcaseSurface` is exactly
   `Standalone|HostWm|SimpleOsWm` with three `*_ready` bits, and
   `showcase_surface_supported` matches exhaustively. `Web`/`Raw2d` variants must
   land before any readiness bit can represent four targets.
5. **CONFIRMED, both halves — highest-value finding.** Two `malloc`s plus three O(n)
   passes per blended row (`runtime_simd_dispatch.c:1464-1476`), and the
   malloc-failure fallback is *also* per-pixel unbox/blend/box, so there is no
   allocation-free path at all. Pixels are boxed `int64_t` via
   `engine2d_box_pixel`/`unbox_pixel` (:663/:667), not packed u32.
   **Consequence: any WS-D kernel design assuming packed u32 SIMD lanes is invalid**
   — D2 must either box-aware-unpack once per span or attack the boxing itself.

Settled disputes: `RenderBackend` has **eight** importers (WS-B right; the ~15
`std.gpu.engine2d.backend` files are a same-named but *different* trait).
`FramebufferBackend` implements `RenderBackend` at `fb_backend.spl:133` — WS-A right
on the trait, wrong on the line number (not :121); `CompositorBackend` is declared at
`display_backend_core.spl:7` and is not implemented there.

## Research (complete, 2026-08-06)
Five parallel agent sweeps. Full findings in the design doc:
`doc/05_design/os/desktop/screen_backend_selection_and_shared_showcase.md`.

Load-bearing facts:
- `CompositorBackend` trait already exists with 6+ implementors; the gap is a
  factory + boot selection (`init_services.spl:179` hardcodes BGA 1024x768).
- rc.conf is boolean-only + key-whitelisted; cannot express `screen_type` today.
- `DrawIrV3Scene` is the real shared render contract — GUI and Web already both
  produce it. `RenderBackend` is imported by **8** targets and **IS implemented
  twice** (`fb_backend.spl:133`, `browser_backend.spl:307`) — the earlier
  "never impl'd" claim was refuted by cross-review. Two distinct live traits share
  the name `RenderBackend`; do not conflate them.
- PS/2 keyboard+mouse exist but polled-only (no IRQ1/IRQ12); no `HalInput`;
  `InputEventQueue` has zero consumers; two incompatible `MouseEvent` types.
- 2D slowness root causes: interpreter extern bridge repacks whole framebuffer per
  span; SIMD alpha-blend is net-negative (gather/scatter, no in-place `blend_span`);
  `simd_fill_row` slower than scalar; blit never SIMD; `dirty_tiles` marked but read
  by nobody; no batching/double-buffer. Evidence: p50 2389 ms vs Cairo 0.032 ms.
- virtio-gpu 2D driver + MapBar/AllocDma syscalls real; Vulkan/Venus is stubbed.

## Acceptance Criteria
- AC-1: `/etc/rc.conf` `screen_type="wm|2d|web|gui"` selects the boot screen through a
  `CompositorBackend` factory, fail-closed against `SimpleOsRuntimeProfile` caps with
  documented fallback; default `wm` preserves today's boot exactly.
- AC-2: All four screens boot in QEMU with nonblank QMP screendump + serial marker
  evidence per screen type; no screen type may claim pass without its artifact.
- AC-3: One `ScreenHost` interface (`present_scene(DrawIrV3Scene)` + `poll_input()
  -> HostInputEvent?`) is the ONLY per-target code; a dependency check proves showcase
  modules import only render-land + `ScreenHost`.
- AC-4: One shared `showcase_core` (toolbar, scrollpane+scrollbar, linked panels,
  event probe) renders on all four targets from byte-identical logic; the existing
  hand-drawn `widget_showcase_gui.spl` is migrated onto the shared pipeline.
- AC-5: Click, drag, and keytype originating at the real host/driver boundary are
  observed in the showcase probe pane on every target, with captured transcripts.
- AC-6: Keyboard+mouse reach simple-2d through one event type and one queue: dual
  `MouseEvent` removed, `InputEventQueue` revived with real consumers, IRQ1/IRQ12
  handlers registered with polling retained as fallback, mouse wheel fixed end-to-end.
- AC-7: 2D perf: in-place `blend_span`/`blit_row` native kernels replace all
  gather/scatter paths, interpreter extern bridge is O(count) not O(framebuffer),
  damage-driven present consumes the already-marked dirty tiles, and every change
  lands with a before/after bench delta from a pinned worktree + deployed native
  binary. No claim without a bench row.
- AC-8: SIMD is configurable (`screen_simd`/`SIMPLE_2D_SIMD` = auto|off|sse2|avx2|neon
  plus per-kernel toggles) and the interpreted default is chosen by measurement.
- AC-9: Vulkan on SimpleOS negotiates real virtio-gpu 3D/Venus capsets, submits over a
  real ring transport, and proves device-origin readback; modeled responses are removed,
  not relabeled. QEMU-scoped with the physical-board gap filed explicitly.
- AC-10: Every AC has an SSpec scenario with real assertions; no mock-in-the-middle, no
  fixture-only renderer bypass, no readiness bit flipped without a captured artifact.

## Scope Exclusions
- TUI cell-grid → DrawIrV3 bridging (stays as-is).
- `app.ui.render` string contract (untouched).
- virgl full GL — Venus/Vulkan path only.
- Physical-board GPU display evidence (virtio-gpu is a QEMU device; gap filed per
  `.claude/rules/board-runnable.md`).

## Traps found during implementation (propagate to anyone touching these)
- **Scroll assertions pass vacuously.** Neither the `max_height` prop nor
  `with_height` on a scroll container creates overflow: layout gives the container
  the parent's spare height (186px) then **shrinks its children to fit** (rows
  measured 2–10px). `_scroll_max_offset` stays 0, the panel silently refuses to
  scroll, and every scroll assertion passes against 0. **Fix: pin each ROW's height**
  (`SC_ROW_H=24`). Any host or spec doing scroll work needs this.
- `match` on a `u8` scrutinee does **not** match integer-literal patterns — every arm
  falls through to `case _`. This had silently broken the entire PS/2 keyboard
  (`scancode_to_key` returned `Key.Unknown` for every key). Widen to `i64` first;
  `virtio_input_ops.spl:146` notes the same sidestep for evdev.
- Three plan-doc signatures were wrong vs source: `widget_scrollbar_pointer_move`
  takes 4 args (no `px`); `widget_scrollbar_pointer_down` returns `text`, not bool;
  `draw_ir_v2_to_v3` is single-arg.
- `node_rect` runs a full `compute_layout` — never call it per coordinate. The
  interpreter's 10M-op budget is the binding constraint on showcase tree size.
- `ScreenHost` lives in its own `screen_host.spl`, NOT `backend.spl`: putting it in
  `backend.spl` would drag `draw_ir_v3` transitively into all 8 `RenderBackend`
  importers, including the two OS-side files.

## Immediate follow-up (ready to do, not yet done)
`key_code.spl` now exists with the canonical VK/W3C space, but
`host_input_event.spl:22-27` still carries the "code space is UNASSIGNED / stopgap"
comment and `host_key_name` has not been delegated to `canon_key_name`. Wire them
together and delete the stopgap note. Then route each producer through its mapper
(`ps2_set1_to_canon`, `evdev_to_canon`, `winit_keycode_to_canon`,
`sdl_keysym_to_canon`) — note `ps2_keyboard.scancode_to_key` covers only 0x01–0x39
and needs the E0-prefixed block, which requires a 16-bit parameter (`0xE000|byte`),
and the 4 duplicate SDL `parse_virtual_key` copies should call the shared mapper.

### 2026-08-21 ARM64 compiler recovery receipt

- Fresh no-stub Phase 2 admitted on source `68a4eea1c13d`: SHA-256
  `d2d89487dbba5249003f5f7c85b1deda96b31980d3b133ce10112121c0c914e2`,
  714 compiled / 0 cached / 0 failed, sanity and struct-receiver gates PASS.
- Exact Rust-seed `Map.for_each` regression passed 8/8. Current `main` now owns
  the superseding generalized implementation in `fd40b997a913`.
- Phase-2 SMF compilation of the imported-composite regression remained
  fail-closed on `Module`/`BlockValue` dependency materialization; no SMF was
  produced.
- A bound Phase-3 planner receipt was produced and Stage 3 started, but external
  deletion of the temporary workspace removed the ignored build artifacts before
  completion. This is neither Stage-3 admission nor QEMU evidence.
- Resume from `/Users/ormastes/simple-dd4c-qemu-recover` on current `main` with a
  fresh Phase-2/receipt pair, then Stage 3, full-CLI producer, ARM64 QEMU RAMFB +
  QMP input capture, and unchanged fail-closed 2D/Web/GUI/WM assertions.

## Unowned gaps (cross-review; assign before the AC they gate can pass)
- **Key-code vocabulary has no owner.** Three producers (PS/2 scancodes, SDL keysyms,
  evdev codes) in three different code spaces feed one `Key(code)` field. This
  directly breaks AC-4's byte-identical-logic claim — the same keypress yields
  different codes per target. Needs a canonical vocabulary + per-producer mapping.
- **No `CompositorBackend` ↔ `ScreenHost` adapter.** WS-A produces the former, WS-B
  consumes the latter, and no plan creates the bridge.
- **`fb_backend.spl` / `browser_backend.spl` owned by nobody** — WS-B disclaims them
  to WS-A/WS-C; neither lists them. They hold the two real `RenderBackend` impls.
- **No screen app shells.** C5 depends on a `screen_app_2d.spl` that no plan creates.
- **No host dispatcher for `SIMPLE_SCREEN_TYPE`.**

## Resolved interface conflicts (cross-review rulings — do not relitigate)
- `HostInputEvent`: **WS-B wins** on arity (5 fields, not 7) and width (`i64`, not
  `i32`). No `dx`/`dy` — no consumer reads them.
- **Wheel sign: WS-B wins — positive = scrolls down**, matching PS/2 native
  positive-Z. WS-C's planned negation is dropped; no layer negates.
- A5 and E4 both rewrite `check_simpleos_multiconfig_live_evidence.spl` and
  `simpleos_config_matrix.spl:594` — **E4 lands first, A5 appends.**
- **WS-D's D1 is near-empty and re-scoped**: the claimed "second implementation" in
  `nogc_async_mut/gpu/engine2d/` is actually a 21-line and a 9-line facade; exactly
  one `fn simd_blend_row` exists. Nothing to delete. D2 is the real work.
- Umbrella WS-D task IDs are off-by-one against the detail plan; the detail plan wins.

## Successor goals (2026-08-06): render-perf redesign critical path

From `doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md` (diagnosis:
`doc/01_research/ui/perf/render_perf_diagnosis_2026-08-06.md`). Fail-closed ACs:

- **F1 class reference semantics** — class-field assignment is
  reference-preserving and struct assignment value-preserving on interpreter,
  seed JIT, and pure-Simple JIT/AOT. AC: one shared reducer corpus produces
  identical hashes on every engine; the sabotage variant (value-copy class
  assignment) turns the gate red. Evidence anchor: the workaround note at
  `src/lib/nogc_sync_mut/ui/draw_ir_v3_native_writer.spl:14-19` becomes
  deletable.
- **F2 packed span ABI** — `BufferSpanRef` → one-shot native resolution, C-side
  `SimplePackedSpanV1`. AC: native kernel observes the original backing
  address; allocation and copy counters are 0 across a batch; a stale
  generation is refused (typed error, not nil). Interpreter mode routes to the
  scalar oracle and must not report SIMD identity.
- **F3 direct column arena writer (V2)** — new `ui_scene_column_arena_v2.spl` +
  `draw_ir_v3_direct_writer_v2.spl`; frozen v3 schema untouched. AC: two warm
  generations with unchanged allocation counter and zero commit-copy bytes;
  partition overflow yields a typed refusal; producer IDs arena-absolute.
- Gate for all three: perf receipts name the engine identity (F0) and fail
  closed on interpreter/seed identity for performance claims.

## Plans
- Perf redesign (successor): `doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md`
- Umbrella: `doc/03_plan/os/simpleos/screens_showcase_2d_opt_plan.md`
- Detail (per workstream, `doc/03_plan/os/simpleos/screens/`):
  - `ws_a_config_screen_selection_detail.md`
  - `ws_b_screenhost_showcase_detail.md`
  - `ws_c_input_hal_detail.md`
  - `ws_d_2d_perf_detail.md`
  - `ws_e_vulkan_detail.md`

## Related Lanes (do not duplicate)
`wm_gui_web_2d_host_env_hardening` (test_host_env + coverage ACs),
`simpleos-multiconfig-vulkan-wm` (evidence gates/wrappers),
`simple-wm-host-simpleos-fullscreen` (host/SimpleOS fullscreen WM),
`simpleos-qemu-wm-real-screen` (ARM64 real-screen evidence),
`simple-gui-2d-render-perf`, `web-wm-authoritative` (CLOSED).

## Model Policy
Sonnet by default with per-task file lists and explicit acceptance. Opus for:
`ScreenHost`/`HostInputEvent` interface design, input event-type unification, IRQ
wiring, native+interpreter SIMD kernels, compositor backing-store/occlusion, and the
Venus transport.
