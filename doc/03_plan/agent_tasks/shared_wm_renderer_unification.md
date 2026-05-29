# Shared WM Renderer Unification — Plan

Date: 2026-05-29

## Current Status

Local agent research found the requested end state is now partially implemented. Existing contracts cover the shared web render API in `src/lib/common/ui/web_render_api.spl`, concrete Web/Electron/Tauri consumers, and concrete CPU/Metal/CUDA Engine2D backend files. Remaining work is to keep the docs/specs aligned with those API files, prove pure Simple browser parity, and close any host WM versus SimpleOS WM service/core gaps.

2026-05-29 recovery note: the active shared-renderer session
`rollout-2026-05-29T04-59-01-019e7219-9d9f-7351-a37a-67b45c65584f.jsonl`
was interrupted while `web_surface_blit_test` was still alive. Resume with a
read-only reconciliation first, then rerun the stalled test with an explicit
timeout and log capture before making new boundary edits.

## Recommended Path

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
5. Rerun the previously stalled `web_surface_blit_test`; if it stalls again,
   record command, duration, last output, and process cleanup result before
   retrying.
6. Keep this lane separate from GUI size/performance and GTK comparison work in
   `doc/03_plan/simple_gui_wm_restart_2026-05-28.md`.

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

- Whether `UI_SURFACE_KIND_TAURI` should be added or whether Tauri remains represented through capability policy without a distinct surface kind.
- Whether CUDA must become a real accelerated renderer in this feature or remain a capability-gated backend that returns unavailable without pretending to render.
- Whether host TUI is in scope for this goal or should remain an explicit unsupported backend while Web/Electron/Tauri/pure Simple are unified.
