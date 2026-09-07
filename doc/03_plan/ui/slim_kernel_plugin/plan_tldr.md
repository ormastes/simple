# TL;DR — slim UI kernel/plugin plan

- Acceptance = UI-SLIM-001..012; done = real minimal TUI + GUI on preserved APIs, verified
  closures, full products intact, before/after numbers on pinned artifacts.
- Wave 0: ownership ledger + benchmark harness (+ macOS rows). Wave 1 (smallest slice):
  `screen.spl` span batching + frame builder, thin TUI route adapter, composition adapter,
  C reference fixtures. Wave 2: event wait/watch, Tiny (after lane transfer), packs.
  Wave 3: integrate, serialized measurement, certification.
- Blockers stated: mac baseline needs deployed pure-Simple `ui`; Tiny files owned by the
  open `tiny_ui_web_wm` lane; async kernel_plugin absent; 800-module cap not redeployed.
- Never start with dynSMF default-on, SIMD/GPU kernels, or a TUI rewrite.

<!-- sdn-diagram:id=ui_slim_kernel_plugin.plan_tldr -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_slim_kernel_plugin.plan_tldr hash=sha256:auto render=ascii
@layout dag
@direction LR

W0 -> W1
W1 -> W2
W2 -> W3
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_slim_kernel_plugin.plan_tldr hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->
