<!-- codex-design -->
# WM/GUI/Web/2D Host Environment Hardening Architecture

## Decision

Extend the existing hosted production route with one hosted-only semantic Web
session bridge and one test-host evidence command. Do not create another input
driver, compositor, renderer, backend abstraction, or capture protocol.

<!-- sdn-diagram:id=wm_gui_web_2d_host_env_hardening.architecture -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_gui_web_2d_host_env_hardening.architecture hash=sha256:auto render=ascii
@layout dag
@direction LR

WinitInput -> HostedEntry
HostedEntry -> HostCompositor
HostCompositor -> HostedWebContentSession
HostedWebContentSession -> BrowserSession
BrowserSession -> HostCompositor
HostCompositor -> SharedWmScene
SharedWmScene -> DrawIrComposition
DrawIrComposition -> Engine2D
Engine2D -> DeviceReadback
DeviceReadback -> HostedWmEvidence
TestHostEnv -> ExistingCapabilityProbes
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_gui_web_2d_host_env_hardening.architecture hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

## Components

| Component | Responsibility | Dependency rule |
|---|---|---|
| `os.hosted.hosted_entry` | Receives real winit events and correlates event/frame evidence | May depend on compositor and hosted bridge |
| `os.compositor.host_compositor_core` | Owns top-window/content hit geometry, content mutation, damage, canonical composition | Must not depend on hosted/browser test code |
| `os.hosted.hosted_web_content_session` | Maintains per-window `BrowserSession`, layout hit-test, DOM click/text dispatch | Hosted-only adapter; no compatibility renderer |
| `os.hosted.hosted_wm_evidence` | Existing command/snapshot/input receipt protocol | Extend existing receipt; no second protocol |
| `os.desktop.shell` + `os.services.wm` | Convert the retained SimpleOS content target to canonical WM IPC | One convergence point; no per-architecture sender |
| `os.userlib.window` | Decode the stable event wire contract for the owning app | Real nonzero IPC port required for system proof |
| `app.test.test_host_env` | Aggregates existing SIMD, Vulkan, RenderDoc, display/input, and readback probes | Test executable only; no production hot-path import |
| `common.ui.host_env_contract` | Pure capability/receipt status and validation functions | No env, process, runtime, or backend calls |
| Existing coverage evaluator/extern owners | Retain stable AST decision identities and merge runtime decision SDN | No parallel collector or schema |

## Selected Flow

1. Winit emits a real pointer/key/text event.
2. `HostCompositor` resolves WM chrome or top client-content coordinates.
3. Client content routes through the persistent `BrowserSession`; DOM hit-test
   and default/author actions mutate the live document, while only executed
   listener/author actions count as application callbacks. A shared monotonic
   counter preserves nested dispatches; hosted receipts expose per-event deltas.
4. The bridge writes mutated body HTML through the compositor owner, which
   marks damage and advances the existing content revision.
5. The existing `SharedWmScene -> DrawIrComposition -> Engine2D` path submits.
6. Existing backend provenance/readback and hosted snapshot fields bind the
   same event ID to the resulting frame.

## Rejected Patterns

| Pattern | Reason |
|---|---|
| Synthetic UI event queue as system proof | Does not originate at screen/host boundary |
| New headless renderer or fixture painter | Creates a mock middle and cannot prove production routing |
| BrowserSession inside shared compositor core | Expands bare-metal dependency closure and startup cost |
| CPU mirror labeled Vulkan/WebGPU proof | Contradicts device-origin readback requirement |
| Screenshot labeled RenderDoc proof | Lacks a valid `.rdc` command-stream capture |
| New runtime externs | Existing facades/probes already provide required capabilities |

## Performance and Invalidation

The hosted bridge is persistent per window. It reparses only when authoritative
window content changes outside the session or dimensions require relayout.
DOM mutation invalidates that window’s content revision and compositor damage;
unchanged frames retain the existing cache/no-present behavior. Diagnostics use
existing `std.diag` timers/events and remain disabled by default.

The shared WM pixel backend keeps row replication on the runtime-owned
`rt_memcpy`/`rt_memset` path so interpreter tests and native/QEMU rendering use
the same fast memory operations.

## Host Rows

Linux x86 is the first mandatory live slice. ARM NEON and RISC-V RVV accept
complete retained `native_host` receipts on any coordinator; absent or
emulated receipts remain active blocked rows with exact resume commands.
Browser Vulkan and RenderDoc-native rows use their existing retained evidence.
Emulation and source inspection alone are correctness support only.

## SimpleOS Remote-Client Admission

SimpleOS screen input is production-routed through the compositor and shell,
but a no-mock system PASS additionally requires a guest app that executes
`WindowClient`. Resident placeholder tasks and shell-materialized owner-port-0
windows are WM/render evidence only. Admission requires ordered QMP input,
pointer IRQ, content hit, `COMP_FOCUS_CHANGED`/`COMP_INPUT_EVENT` send, client
receipt, visible app mutation, later frame generation, and changed `pmemsave`
bytes for the same window.
