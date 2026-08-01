# Theme rendering and WM host/simpleOS sync state (2026-07-25)

## Current code changes in progress
- Fixed WM/theme IDs to use active WM theme snapshots (with default fallback) instead of hardcoded `dark` / `aetheric_dark` in:
  - `src/app/ui.web/wm_bridge.spl`
  - `src/app/ui.web/_HostTaskbarRuntime/mode_and_layout_helpers.spl`
  - `src/app/ui.web/server.spl`
  - `src/app/ui.web/html.spl`
  - `src/os/compositor/wm_action_applier.spl`
  - `src/os/compositor/simple_gui_window_renderer.spl`
  - `src/os/compositor/host_wm_theme_bootstrap.spl`
  - `src/os/compositor/simpleos_wm_theme_bootstrap.spl`
- Theme fallback strategy now:
  - prefer active WM chrome snapshot if present;
  - else apply and use default package snapshot;
  - else fallback to existing aetheric-generated snapshot.
- Current follow-up work in progress:
  - Fixed WM render-envelope propagation in `src/app/ui.web/wm.js` so `renderWindow` and reopened `openWindow` updates now apply `css` and `root_attrs` (plus stale theme attributes are replaced on the document root).
  - Fixed Pure-Simple renderer custom-prop extraction in `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl` to include `:root[...]` variant selectors.
  - Fixed `src/lib/gc_async_mut/gpu/browser_engine/style_block_resolve.spl` to treat `:root[...]` as root-element selectors during attribute matching.
- Remaining checks to run:
  - Re-run `check-simpleos-wm-visible-display-evidence` once grub tooling is available.
  - Re-run host + qemu WM render parity checks after this commit.
## 2026-08-01 GH sync and renderer/IR check

Ran `git fetch` and synced `tmp-docfix` context against `origin/main` now at `57923b8259` (from `fe481ab069`).
- New upstream commit since the last recorded sync:
  - `57923b8259` `fix(hir): keep the operator when lowering augmented assignment`
    - `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs`
    - `test/01_unit/compiler/compound_assign_lowering_spec.spl`
    - `doc/08_tracking/bug/jit_struct_field_compound_assign_loads_zero_2026-07-27.md`
- "runderer"/runner search against upstream branch refs/docs/code returned no new match.
- IR-spec check:
  - No new `*_spec.spl` changes related to renderer backend runners were included in `57923b8259`; IR/spec-impact remains from existing DrawIR work already tracked in prior runs.
- Plan impact: upstream change is compiler-HIR scope only (non-blocking for current WM/theme rendering lane). Keep local theme-state and capture/evidence tasks as-is.
  - Continue focusing on:
    - hosted theme input (`SIMPLE_WM_THEME_FILE`)
    - SimpleOS theme file (`/THEME.CSS`)
    - web-window themed payload propagation and envelope fidelity.

## Historical upstream renderer/IR context tracked

- `fe481ab069` `refactor(ui): S1 DrawIR Vulkan-canonical enums + ResourceTable.formats u32`
  - `src/lib/common/ui/draw_ir_v3.spl`
  - `src/lib/common/ui/draw_ir_v3_backend_enums.spl`
  - `src/lib/nogc_sync_mut/engine/render/vulkan_backend3d.spl`
  - `test/01_unit/lib/common/ui/draw_ir_v3_backend_enums_spec.spl`
  - `test/01_unit/lib/common/ui/draw_ir_v3_spec.spl`
- `f80696b851` `fix(hosted-wm): repair four unparseable source sites blocking the hosted entry closure`
  - `src/lib/gc_async_mut/web/browser_session_runtime.spl`
  - `src/os/hosted/hosted_browser_renderer_worker.spl`
  - `src/os/hosted/hosted_web_content_session.spl`
  - `doc/08_tracking/bug/hosted_wm_entry_closure_unparseable_grammar_gaps_2026-08-01.md`
- `69d3e4db82` `fix(parser): continue a logical line when the next line STARTS with a binary operator`
  - `src/compiler/10.frontend/core/lexer_struct.spl`
  - `src/compiler/10.frontend/core/tokens.spl`
  - `test/01_unit/compiler/parser_leading_operator_continuation_spec.spl`
- `6061fb7ed4` `fix(native-link): stop calling __module_init_dynamic twice`
  - `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs`
- `b47e4212c1` `fix(parser): slice bound s[:end] was parsed as an index by symbol literal`
  - `src/compiler_rust/parser/src/expressions/postfix.rs`
  - `test/01_unit/std/runtime_parser_bugs_spec.spl`
- `33754b8df0` DrawIR backend-native layout architecture/docs update
  - `doc/03_plan/ui/draw_ir/draw_ir_backend_native_refactor_plan.md`
  - `doc/03_plan/ui/draw_ir/draw_ir_backend_native_refactor_plan_tldr.md`
  - `doc/04_architecture/ui/rendering/draw_ir_backend_native_layout.md`
  - `doc/05_design/ui/rendering/draw_ir_multibackend_design.md`
- `cf04652906` `docs(ui): record S1 finding — runtime usage bits are RT-local, not VkImageUsageFlagBits`
  - `doc/04_architecture/ui/rendering/draw_ir_backend_native_layout.md`
- `f18c596313` `fix(seed): implement array .at() as a real Option accessor on the interpreter`
  - `doc/08_tracking/bug/array_at_returns_nil_for_every_index_2026-08-01.md`
  - `src/compiler_rust/compiler/src/interpreter_method/collections.rs`
  - `test/01_unit/lib/common/array_at_option_spec.spl`
Plan impact: upstream introduced parser/HIR and DrawIR architecture updates plus hosted-closure fixes. Continue local theme-state tracking and capture/evidence hardening focused on:
  - hosted theme input (`SIMPLE_WM_THEME_FILE`)
  - SimpleOS theme file (`/THEME.CSS`)
  - web-window themed payload propagation and envelope fidelity.

## Parallel agent findings (host + QEMU)
- `check-hosted-wm-capture-evidence.shs`: diagnostic pixels only; production
  admission fails on the Rust seed warning, empty theme manifest hash, local
  raster fallback, and absent event/performance binding.
  - Evidence in `build/hosted-wm-capture-evidence/*` and
    `doc/09_report/hosted_wm_capture_evidence_2026-07-25.md`.
  - Backend currently uses local Web raster readback; Metal GPU submit/readback remains unhooked.
- `check-simpleos-x86-64-wm-qemu-preflight.shs`: PASS.
- `check-simpleos-x86-64-wm-qemu-readiness.shs`: FAIL on this host (`grub-mkstandalone` missing), so boot path blocked.
- `check-simpleos-arm64-wm-qemu-readiness.shs`: PASS.
- `check-simpleos-wm-visible-display-evidence.shs`: FAIL on this host for the same grub tooling blocker.
- `doc/09_report/simpleos_wm_visible_display_evidence_2026-07-25.md` added by validation run.
