# Slim TUI/GUI — kernel/plugin composition design

**Date:** 2026-09-05 · **Base:** HEAD `56dd3059c2e`
**Research:** `doc/01_research/ui/slim_kernel_plugin/` (external design + repo verification addendum)
**Prior architecture reused:** `doc/04_architecture/compiler/plugin_arch/kernel_pluggable_partition.md`,
`doc/04_architecture/tiny_ui_web_wm.md`, `doc/04_architecture/ui/simple_gui_stack.md`

## Decision

Keep the public UI API and the existing UI model. Split each UI product into a
**composition kernel** (the already-landed `std.nogc_sync_mut.composition` subset:
`SimpleProviderQueryV1` discovery/admission, static registry table, SCI codec) plus
**selected providers** (one terminal OR one host window; one renderer) plus
**declared feature packs** (parser, watcher, WM, DrawIR/WebIR adapters, GPU). No new
runtime, loader, manifest language, grammar, or UI tree. "Kernel" is the application
composition kernel, never the SimpleOS kernel. The async `kernel_plugin` layer from the
lint plan does not exist; this design uses **static composition** now and consumes that
layer when it lands — it does not build it.

## Adaptations to the external design (verified against the repo)

| External assumption | Repo fact | Design consequence |
|---|---|---|
| GUI host entry "to be established" | `src/app/ui/main.spl` dispatches; `host_gui.spl` is the real window host | A00 ledger names these owners on day one |
| Tiny files are free to edit (A04/A05/A07) | Owned by the OPEN `tiny_ui_web_wm` lane, review FAIL | Tiny work sequences after that lane or via explicit transfer; Wave 1 is normal-TUI only |
| SMF provider placement for packs (A10) | dynSMF default-on is NO-GO with reopen gates | packs are static-composed until the reopen gates pass |
| Baseline from current binary | `bin/simple` here is a bootstrap shim | baseline BLOCKED on mac; seed lane = diagnostic only |
| TUI hello loads compositor "possibly" | `async_app` closure = 344 files incl. drivers/kernel/skia | P08 thin route adapter is a first-wave item |

## Composition recipes (data, not syntax)

| Recipe | Kernel subset | Providers | Packs at startup | Packs on demand |
|---|---|---|---|---|
| `tui-hello-static` | provider contract + static table | terminal (ANSI/termios) | none | none |
| `tui-file-watch` | same | terminal | `.ui.sdn` parser, watcher (required by contract) | none |
| `gui-hello-static` | same | host window + one renderer + text | none | none |
| `ui-full-static` | same | selected platform path | all current | none, but unused ones do not initialize |
| `ui-full-demand` | same + generated index | selected | required closure | coarse packs, first-use timed (X1) |

Each feature carries two independent states: **requirement** (ready / on-action / absent)
and **placement** (static / native shared lib / SMF / worker). Sealed hello recipes are
static: no directory scan, no manifest parse, no loader thread.

## Owners and seams

| Seam | Module | Change class |
|---|---|---|
| Provider admission | `src/lib/nogc_sync_mut/composition/provider_contract.spl` | read-only; reused |
| Static table | `src/lib/nogc_sync_mut/tiny/common/static_registry.spl` pattern | reused; UI adapter `src/lib/nogc_sync_mut/ui/composition_adapter.spl` (new, A02) |
| TUI route | `src/app/ui.tui/async_app.spl:29` host-compositor import | thin selected-route adapter (P08) |
| Normal screen | `src/app/ui.tui/screen.spl` | P01/P02 private frame builder, publish one `Screen` snapshot; COW preserved |
| Event wait | `src/app/ui.tui/async_app.spl` | P06/P07 block on channel/deadline; watcher contract unchanged |
| Tiny layout/render/software | `src/lib/nogc_sync_mut/tiny/**` | P03/P04/P05/P10/P11 — after Tiny lane transfer |

Invariants UI-SLIM-001..012 from the external design are the acceptance IDs (see plan).
Guardrails carried over verbatim: a `ch: text` is not one cell (prove one-cell path,
fall back otherwise); never reuse storage a published `Screen` still references;
RGB565 `[i32]` stays a public contract; stream validation and receipts never disabled.

<!-- sdn-diagram:id=ui_slim_kernel_plugin.design -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_slim_kernel_plugin.design hash=sha256:auto render=ascii
@layout dag
@direction TB

app_entry -> recipe
recipe -> composition_kernel
composition_kernel -> provider_admission
provider_admission -> terminal_provider
provider_admission -> host_window_provider
composition_kernel -> ui_essentials
ui_essentials -> screen_or_tinypane
screen_or_tinypane -> selected_renderer
recipe ~> demand_packs
demand_packs -> parser
demand_packs -> watcher
demand_packs -> shared_wm
composition_kernel -x shared_wm
terminal_provider -x gpu
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_slim_kernel_plugin.design hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->
