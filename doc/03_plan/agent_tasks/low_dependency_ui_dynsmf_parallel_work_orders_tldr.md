# Low Dependency UI dynSMF Parallel Work Orders TLDR

- Agent A: UI import-closure gates.
- Agent B: dynSMF session lifecycle.
- Agent C: stdlib dynSMF manifests and opt-out policy.
- Agent D: HTML/CSS component capability loading.
- Agent E: specs, manuals, verification, and doc layout guard.
- Final implementation still waits for selected requirements.

```sdn
parallel_work {
  A_ui_boundary + B_session
  B_session -> C_manifest_policy
  A_ui_boundary -> D_html_css
  A_ui_boundary + B_session + C_manifest_policy + D_html_css -> E_verify
}
```
