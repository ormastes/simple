# TL;DR — slim UI kernel/plugin design

- Kernel = existing `nogc_sync_mut.composition` subset (provider query/admission, static
  table, SCI codec). Providers = one terminal OR one host window + one renderer. Packs =
  parser, watcher, WM, DrawIR/WebIR adapters, GPU — declared, static now.
- No new runtime/loader/grammar/UI tree. Async `kernel_plugin` is consumed when the lint
  lane lands it, never built here.
- Recipes: `tui-hello-static`, `tui-file-watch`, `gui-hello-static`, `ui-full-static`,
  `ui-full-demand`. Requirement and placement are independent states.
- First seams: `screen.spl` private frame builder (COW kept), `async_app.spl` thin route
  adapter + blocking wait, new `ui/composition_adapter.spl`. Tiny seams wait for the open
  Tiny lane.
- Guardrails: one-cell fast path only, no storage reuse behind a published `Screen`,
  RGB565 `[i32]` contract kept, validation/receipts never disabled.

<!-- sdn-diagram:id=ui_slim_kernel_plugin.design_tldr -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_slim_kernel_plugin.design_tldr hash=sha256:auto render=ascii
@layout dag
@direction LR

recipe -> composition_kernel
composition_kernel -> provider
provider -> renderer
recipe ~> packs
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_slim_kernel_plugin.design_tldr hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->
