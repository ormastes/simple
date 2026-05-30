# Shared WM Renderer Unification — Plan

Date: 2026-05-29

Precedence: this is a lane note and evidence record, not the authoritative
focused restart status. Use `doc/03_plan/gui_renderer_restart_plan_2026-05-29.md`
for the focused GUI renderer restart status and
`doc/03_plan/shared_wm_renderer_unification_completion_audit.md` for the
broader shared-WM completion audit.

## Current Status

Local agent research originally found the requested end state partially implemented. Current recovery evidence has since closed the shared web render API, CPU/Metal/CUDA Engine2D interface, host WM/SimpleOS WM lifecycle sharing, shared web renderer API, and shared 2D compositor API rows in `doc/03_plan/shared_wm_renderer_unification_completion_audit.md`. The remaining shared-WM audit gap is the Qt size/memory comparison row, because Qt Widgets development files are not available on this host. The focused GUI renderer restart has rechecked pure Simple renderer behavior (`simple_web_renderer_spec` `29/29`, bounded browser smoke `4/4`) and Web/Tauri/UI-layer contracts.

2026-05-29 recovery note: the active shared-renderer session
`rollout-2026-05-29T04-59-01-019e7219-9d9f-7351-a37a-67b45c65584f.jsonl`
was interrupted while `web_surface_blit_test` was still alive. The recovery
has been performed: the old stalled `_test.spl` coverage was replaced by the
bounded `_spec.spl` coverage recorded below.

## Historical Recommended Path

Recommended selection: Feature Option C with NFR Option 3 if the goal is to make the complete objective true. If the next turn should be lower risk, choose Feature Option B with NFR Option 2 first, then follow with WM service unification.

## Implementation Phases

1. Finalize requirements after user selection.
2. Maintain shared web render API docs/specs:
   - Treat `src/lib/common/ui/web_render_api.spl` as the canonical request/artifact/capability API.
   - Keep Web/Electron/Tauri and pure Simple browser participation covered by one conformance spec.
   - Track host window command serialization separately in `src/app/ui.web/host_adapter_contract.spl`.
3. Maintain Engine2D API convergence:
   - Treat `src/lib/gc_async_mut/gpu/engine2d/backend.spl::RenderBackend` as the mandatory primitive API.
   - Make session APIs wrap that trait instead of competing with it.
   - Keep `backend_cpu.spl`, `backend_metal.spl`, and `backend_cuda.spl` aligned, with CUDA allowed to report typed unavailable capability.
4. Design WM logic sharing:
   - Remove or replace the local `WmService` in `host_compositor_entry.spl`.
   - Extract any host-only window list mechanics into adapter code below the real WM service/core.
   - Route SimpleOS direct overlay drawing through `CompositorBackend` or `Engine2dCompositorBackend`.
5. Add system tests:
   - Shared web render API parity across Web/Electron/Tauri/pure Simple.
   - Engine2D backend trait conformance for CPU/Metal/CUDA.
   - Host and SimpleOS WM behavior parity for window lifecycle and input routing.
6. Implement in staged patches:
   - Web API first.
   - 2D backend API second.
   - WM service sharing third.
7. Verify:
   - Run focused SPipe specs.
   - Run compiler/lib checks if shared library or compiler-facing imports change.
   - For WM/tooling hot paths, capture warm startup, representative latency, and RSS where applicable.

## 2026-05-29 Resume Plan

1. Re-audit direct GUI/browser/compositor imports of low-level
   `simple_web_renderer` modules.
2. Classify every remaining direct dependency as one of:
   - required low-level implementation detail below the shared API,
   - temporary compatibility shim,
   - boundary violation to remove.
3. Route boundary violations through `src/lib/common/ui/web_render_api.spl` or
   the established common UI adapter surface.
4. Preserve behavior for browser, compositor, pixel backend, Electron, and Tauri
   paths with focused tests before removing old calls.
5. Keep the bounded `web_surface_blit_spec.spl` coverage passing; if it stalls
   again, record command, duration, last output, and process cleanup result
   before retrying.
6. Keep this lane separate from GUI size/performance and GTK comparison work in
   `doc/03_plan/simple_gui_wm_restart_2026-05-28.md`.

## 2026-05-29 Web Surface Blit Recovery

- The old `test/unit/os/compositor/web_surface_blit_test.spl` still stalled
  under `bin/simple test` and left an orphaned `bin/simple run` child until
  cleaned up.
- The coverage was converted to
  `test/unit/os/compositor/web_surface_blit_spec.spl` and bounded to smaller
  fixture dimensions.
- Verification:
  - `SIMPLE_LIB=src timeout 45s bin/simple check test/unit/os/compositor/web_surface_blit_spec.spl`
    passed.
  - `SIMPLE_LIB=src timeout 45s bin/simple test test/unit/os/compositor/web_surface_blit_spec.spl --mode=interpreter --clean --format json`
    passed `7/7` in 3846 ms.
  - 2026-05-29 continuation rerun: the same check passed, and the same
    bounded test passed `7/7` in 4949 ms.

## 2026-05-29 create_web_window Surface Plumbing

- `wm_action_applier.spl` now converts `create_web_window` actions into a
  compositor surface carrying a `WebRenderRequest` with target `simple_web`,
  stable `web_window_{id}` surface identity, viewport dimensions, and pixel
  output enabled.
- `wm_action_applier_spec.spl` covers the shared render request helper and the
  create-web-window action path.
- Verification:
  - `SIMPLE_LIB=src timeout 120s bin/simple check src/os/compositor/wm_action_applier.spl test/unit/os/compositor/wm_action_applier_spec.spl test/unit/os/compositor/web_surface_blit_spec.spl test/unit/os/compositor/simple_web_window_renderer_spec.spl`
    passed.
  - `SIMPLE_LIB=src timeout 80s bin/simple test test/unit/os/compositor/wm_action_applier_spec.spl --mode=interpreter --clean --format json`
    passed `10/10` in 1022 ms.
  - `SIMPLE_LIB=src timeout 80s bin/simple test test/unit/os/compositor/web_surface_blit_spec.spl --mode=interpreter --clean --format json`
    passed `7/7` in 2504 ms.
  - `SIMPLE_LIB=src timeout 80s bin/simple test test/unit/os/compositor/simple_web_window_renderer_spec.spl --mode=interpreter --clean --format json`
    passed `5/5` in 2450 ms.

## 2026-05-29 SimpleOS GUI Adapter Lifecycle Coverage

- Added focused coverage to
  `test/unit/os/compositor/simpleos_gui_shared_wm_adapter_spec.spl` proving
  `SimpleOsGuiAdapter.deliver_bridge_request(...)` routes create, move,
  resize, minimize, and restore through the shared host compositor lifecycle
  path.
- Verification:
  - `SIMPLE_LIB=src timeout 60s bin/simple check test/unit/os/compositor/simpleos_gui_shared_wm_adapter_spec.spl`
    passed.
  - `SIMPLE_LIB=src timeout 60s bin/simple test test/unit/os/compositor/simpleos_gui_shared_wm_adapter_spec.spl --mode=interpreter --clean --format json`
    passed `2/2` in 5240 ms.

2026-05-29 continuation:
- Extended the same adapter bridge proof to set-title, focus, maximize,
  update-tree, and destroy.
- Verification:
  - `SIMPLE_LIB=src timeout 120s bin/simple check test/unit/os/compositor/simpleos_gui_shared_wm_adapter_spec.spl src/os/compositor/host_compositor_entry.spl src/os/compositor/wm_action_applier.spl`
    passed.
  - `SIMPLE_LIB=src timeout 80s bin/simple test test/unit/os/compositor/simpleos_gui_shared_wm_adapter_spec.spl --mode=interpreter --clean --format json`
    passed `3/3` in 5111 ms.
  - `SIMPLE_LIB=src timeout 80s bin/simple test test/unit/os/compositor/wm_action_applier_spec.spl --mode=interpreter --clean --format json`
    passed `9/9` in 487 ms.

## Danger / Possible Crash Adjacent Work

The same interrupted Codex sequence also touched or audited feature-request
work. Treat these as crash-sensitive and resume one at a time after the shared
renderer lane is parked or cleanly paused.

1. SimpleOS feature requests:
   - Tracking: `doc/08_tracking/feature_request/simpleos_os_requests.md`.
   - Risk: QEMU/live checks, paging/timer/VM state, and partial test artifacts
     can survive interruption.
   - Resume with targeted non-live/unit tests before any live guest run.
2. Net acceleration feature requests:
   - Tracking: `doc/08_tracking/feature_request/net_acceleration_requests.md`.
   - Risk: socket/TCP state-machine edits can hang or diverge across blocking
     and nonblocking paths.
   - Resume with focused socket/TCP data-path specs before broader suites.
3. SPM request feature requests:
   - Tracking: `doc/08_tracking/feature_request/spm_requests.md`.
   - Risk: privilege, IPC port binding, and init/register behavior can look
     complete in trackers while focused tests still fail.
   - Resume by running the focused SPM IPC tests matching the dirty files.

Deferred ordered feature-request follow-ups remain
`riscv_baremetal_tp_init_2026-05-02` and
`lzma2_full_lclppb_2026-05-01`; do not start them until the three danger items
above have explicit pass/fail evidence or are deliberately parked.

### Danger Task Progress Log - 2026-05-29

0. Initial reconciliation:
   - Dirty SimpleOS lane files found:
     `doc/08_tracking/feature_request/simpleos_os_requests.md`,
     `test/system/os_network_spec.spl`, and
     `test/unit/os/kernel/arch/x86_32_paging_timer_spec.spl`.
   - Dirty net acceleration lane files found:
     `doc/08_tracking/feature_request/net_acceleration_requests.md`,
     `src/os/services/netstack/socket.spl`,
     `src/os/services/netstack/tcp_connection.spl`,
     `src/os/services/netstack/tcp_state_machine.spl`,
     `test/system/net_tcp_socket_data_path_spec.spl`, and
     `test/system/net_rdma_transport_spec.spl`.
   - Dirty SPM lane files found:
     `test/unit/os/kernel/ipc/spm_init_register_spec.spl` and
     `test/unit/os/kernel/ipc/spm_port_spec.spl`.
   - No source edits have been made in this recovery pass yet.
1. SimpleOS focused non-live verification:
   - `SIMPLE_LIB=src bin/simple check test/unit/os/kernel/arch/x86_32_paging_timer_spec.spl`
     passed.
   - `SIMPLE_LIB=src bin/simple test test/unit/os/kernel/arch/x86_32_paging_timer_spec.spl --mode=interpreter --clean --format json`
     passed `4/4` in 1525 ms.
   - `SIMPLE_LIB=src bin/simple check test/system/os_network_spec.spl`
     passed.
   - `SIMPLE_LIB=src bin/simple test test/system/os_network_spec.spl --mode=interpreter --clean --format json`
     passed `1/1` in 2280 ms.
   - No SimpleOS crash, hang, stale QEMU, or live guest run occurred in this
     recovery step.
2. Net acceleration focused verification:
   - `SIMPLE_LIB=src bin/simple check src/os/crypto/crc32.spl src/os/services/netstack/socket.spl src/os/services/netstack/tcp_connection.spl src/os/services/netstack/tcp_state_machine.spl test/system/net_tcp_socket_data_path_spec.spl test/system/net_rdma_transport_spec.spl`
     passed.
   - `SIMPLE_LIB=src bin/simple test test/system/net_tcp_socket_data_path_spec.spl --mode=interpreter --clean --format json`
     passed `6/6` in 407 ms.
   - `SIMPLE_LIB=src bin/simple test test/system/net_rdma_transport_spec.spl --mode=interpreter --clean --format json`
     passed `7/7` in 164 ms.
   - No netstack crash, hang, retry storm, or blocking/nonblocking readiness
     stall occurred in this recovery step.
3. SPM focused IPC verification:
   - `SIMPLE_LIB=src bin/simple check test/unit/os/kernel/ipc/spm_init_register_spec.spl test/unit/os/kernel/ipc/spm_port_spec.spl`
     passed.
   - `SIMPLE_LIB=src bin/simple test test/unit/os/kernel/ipc/spm_init_register_spec.spl --mode=interpreter --clean --format json`
     passed `4/4` in 2261 ms.
   - `SIMPLE_LIB=src bin/simple test test/unit/os/kernel/ipc/spm_port_spec.spl --mode=interpreter --clean --format json`
     passed `10/10` in 152 ms.
   - No SPM IPC crash, hang, privilege-path stall, or port-registration
     regression appeared in this recovery step.
4. Final danger-task focused verification:
   - Combined `bin/simple check` over all 10 danger-lane source/spec files
     passed.
   - Final focused test pass:
     x86_32 paging/timer `4/4`, OS network `1/1`, TCP socket data path `6/6`,
     RDMA transport `7/7`, SPM init/register `4/4`, and SPM port `10/10`.
   - Process scan after verification found no lingering `qemu-system`,
     `bin/simple test`, or focused danger-lane test processes.
   - Danger tasks are complete for this recovery pass; no crash or hang was
     reproduced.

## Open Decisions

- Resolved: `UI_SURFACE_KIND_TAURI`/the Tauri surface kind is present in the surface registry and covered by focused binding evidence in the completion audit.
- Resolved for this feature: CUDA remains a capability-gated backend. It must
  return typed unavailable diagnostics when hardware/runtime proof is absent
  and must not pretend to render; strict CUDA integration evidence covers the
  available accelerated path and software-mirror fallback behavior.
- Resolved for this feature: host TUI is outside the shared Web/Electron/Tauri
  renderer unification scope. TUI work remains tracked by the editor/TUI lane,
  while Web, Electron, Tauri, pure Simple web, host WM, and SimpleOS WM are the
  unified renderer surfaces for this plan.
