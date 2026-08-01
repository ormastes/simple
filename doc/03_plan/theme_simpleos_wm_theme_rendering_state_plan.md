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

## 2026-08-01 sync-gh follow-up on renderer-runner + IR-spec branch drift

- Pulled `origin` and reviewed `origin/sync-renderer-ir-spec-update` against `origin/main`.
- Notable committed deltas on that branch are:
  - `f7b8526aa8` / `2277b52949`: hosted/web renderer protocol receipt and themed restart hardening
    - Files: `src/os/compositor/simple_web_window_renderer.spl`, `src/os/hosted/hosted_browser_renderer_*.spl`, `src/lib/common/web/browser_renderer_protocol.spl`, plus renderer worker/entry test specs.
  - `2a4bf46c9d`: documentation/spec artifact refresh for renderer+IR spec set.
- I did not merge those commits here because this lane is still focused on SimpleOS WM/theme snapshot + root-attr propagation and host/simpleOS evidence parity; these renderer-runner edits are best consumed by the renderer/backend task owner unless that lane is being merged now.
- Plan impact: no immediate task shift for this lane; keep current local evidence plan and theme-propagation checks.
## 2026-08-01 GH sync and renderer/IR check

Ran `git fetch` and synced `tmp-docfix` context against `origin/main`.
Current upstream tip noted in this branch as `63c362526c` (latest checked).
- New upstream commit since the last recorded sync:
  - `57923b8259` `fix(hir): keep the operator when lowering augmented assignment`
    - `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs`
    - `test/01_unit/compiler/compound_assign_lowering_spec.spl`
    - `doc/08_tracking/bug/jit_struct_field_compound_assign_loads_zero_2026-07-27.md`
- "runderer"/runner search against upstream branch refs/docs/code returned no new match.
- IR-spec check:
  - No new `*_spec.spl` changes related to renderer backend runners were included through `63c362526c`; IR/spec-impact remains from existing DrawIR work already tracked in prior runs.
  - Plan impact: upstream change is compiler-HIR scope only (non-blocking for current WM/theme rendering lane). Keep local theme-state and capture/evidence tasks as-is.
  - Continue focusing on:
    - hosted theme input (`SIMPLE_WM_THEME_FILE`)
    - SimpleOS theme file (`/THEME.CSS`)
    - web-window themed payload propagation and envelope fidelity.
- 2026-08-01 follow-up "runderer/IR" check:
  - Searched recent upstream logs for renderer/backend/IR/spek runner-relevant commits: `fe481ab069`, `f80696b851`, `33754b8df0`, `205b35e474`, plus legacy `51bfb0d970`, `57923b8259`.
  - Impact to this lane: no new renderer runner/IR spec behavior requiring plan adjustment.
  - `f80696b851` (hosted-wm unparseable source fixes) is advisory for hosted-runner stability only.

- 2026-08-01 follow-up "runderer/IR" check (latest range refresh):
  - Compared upstream window: `31c858cab9..63c362526c`.
  - New commit:
    - `4755c8ab52` `feat(ui): S5 backend-stride capacity sizing for one-time GUI IR allocation`
      - `src/lib/common/ui/gpu_web_capacity_strides.spl`
      - `test/01_unit/lib/common/ui/gpu_web_capacity_strides_spec.spl`
    - `61bb1f1fea` `fix(repo): restore full tree wiped by bad plumbing commit + land GAP-2 wiring`
      - `src/lib/common/ui/gpu_web_capacity_strides.spl`
      - `test/01_unit/lib/common/ui/gpu_web_capacity_strides_spec.spl`
      - `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`
      - `src/lib/gc_async_mut/gpu/browser_engine/*.spl` family
    - `63c362526c` `fix(repo): reland 3 commits clobbered by the 61bb1f1feaed tree restore`
      - repeat of the same GAP-2/GPU IR files plus corrected `.mcp.json` state
  - "runderer"/runner search against this range returned no new match.
  - IR-spec impact:
    - no renderer/backend-IR `_spec.spl` protocol behavior changes in this window.
    - one touched unit spec is `test/01_unit/lib/common/ui/gpu_web_capacity_strides_spec.spl` (capacity accounting, not runner dispatch protocol).
  - Plan impact: current lane still unchanged; keep focus on hosted/simpleOS theme propagation and web-window payload fidelity while this DrawIR seam is consumed where needed by backend implementers.

- Additional renderer/IR branch scan (2026-08-01):
  - Checked `origin/sync-renderer-ir-spec-update` for out-of-band renderer runner + IR/spec updates.
  - Notable commit set includes:
    - `f7b8526aa8` `fix(web): preserve themed renderer restarts` and `2277b52949` `test(web): enforce hosted theme receipts` (theme/restart behavior in
      `src/os/compositor/simple_web_window_renderer.spl`, `src/os/hosted/hosted_browser_renderer_*.spl`, and related worker/runtime specs).
    - `2a4bf46c9d` docs+spec synchronization for renderer IR artifacts.
  - Result for this lane: no changes were auto-merged; branch mainly updates host/web renderer docs/specs and protocol hardening.
  - Plan impact: no immediate plan delta for the current SimpleOS theme-state tracking lane; if we expand this task to fully own hosted-web renderer protocol parity, merge/cherry-pick from this branch first.

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

## 2026-08-01 GH sync re-check: renderer/IR-runner spec scan

- Ran `git fetch --all --prune` and compared against `origin/main`.
- Latest runner/IR-related upstream in this range:
  - `118c636ead` `feat(web/2d): land GAP-2 N-stop gradient CSS wiring + l4-stage-a salvage audit` (web2D gradient pipeline wiring + doc updates).
  - `31c858cab9` `refactor(ui): S2 DrawIR backend accessor seam (VK identity, MTL/DXGI remap)`.
- `IR spec` impact scan result:
  - no new `*_spec.spl` files in this lane’s renderer stack changed in those two points;
  - no immediate plan item change required beyond current theme propagation + payload fidelity tasks.
- Known tracking note:
  - upstream `118c...` touched this plan file on main in a different maintenance path; branch remains intentionally on `origin/tmp-docfix` docs lane, so I am keeping this plan as the local lane tracker and logging the delta here.
