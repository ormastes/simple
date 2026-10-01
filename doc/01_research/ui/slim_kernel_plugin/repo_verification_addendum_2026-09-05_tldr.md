# TL;DR — slim UI kernel/plugin, repo verification (2026-09-05)

- External design (from Downloads) verified at HEAD `56dd3059c2e`: all eight source
  observations R02–R08 CONFIRMED with file:line.
- Real entry owners: `src/app/ui/main.spl` (tui/gui dispatch), `src/app/ui.tui/async_app.spl`,
  `src/app/ui_showcase/hosts/host_gui.spl`. `hello_gui.spl` is a TUI.
- Seed-lane `deps fast`: the TUI live-reload app closes over 344 files incl. `os/drivers`,
  `os/kernel`, `lib/skia` via `host_compositor_entry` — import-side proof for UI-SLIM-004.
- Kernel/plugin: `nogc_sync_mut/composition` is landed (28 callers, 35 specs);
  `nogc_async_mut/kernel_plugin` does not exist; lint migration plan is PROPOSED only.
- Tiny lane is OPEN with a FAIL review and owns the Tiny files the external briefs assign.
- Do not repeat: dynSMF default-on (NO-GO), SIMD-first, bottom-up TUI rewrite.
- Baseline is BLOCKED on this mac: `bin/simple` is a bootstrap shim.

<!-- sdn-diagram:id=ui_slim_kernel_plugin.research_tldr -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_slim_kernel_plugin.research_tldr hash=sha256:auto render=ascii
@layout dag
@direction LR

async_app -> host_compositor_entry
host_compositor_entry -> os_drivers
host_compositor_entry -> skia
composition -x ui_tui
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_slim_kernel_plugin.research_tldr hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->
