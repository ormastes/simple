# WM/GUI/Web/2D Host Hardening — TLDR

Reuse the production route and add only a hosted Web semantic-event adapter.

<!-- sdn-diagram:id=wm_gui_web_2d_host_env_hardening.architecture_tldr -->
<details class="sdn-source"><summary>SDN source</summary>

```sdn id=wm_gui_web_2d_host_env_hardening.architecture_tldr hash=sha256:auto render=ascii
@layout dag
@direction LR
Winit -> HostCompositor
HostCompositor -> BrowserSession
BrowserSession -> HostCompositor
SimpleOSInput -> DesktopShell
DesktopShell -> WmService
WmService -> WindowClient
HostCompositor -> DrawIrComposition
DrawIrComposition -> Engine2D
Engine2D -> Readback
```

</details>
<details class="sdn-ascii" open><summary>Diagram</summary>

```ascii generated-from=wm_gui_web_2d_host_env_hardening.architecture_tldr hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

- `test_host_env` aggregates existing probes; it does not own hardware access.
- Hosted semantic dispatch uses persistent `BrowserSession`, never a mock queue.
- Rendering stays `SharedWmScene -> DrawIrComposition -> Engine2D`.
- Existing hosted evidence requires the receipt target to name exactly one
  window in the retained compositor snapshot, then binds it to backend readback.
- SimpleOS content hits now reach WM IPC; a running nonzero-port guest client
  is still required for no-mock QEMU system proof.
- Linux x86 is first; unavailable native rows remain blockers.
