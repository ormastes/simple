# Simple Browser Production Level Plan TLDR

## Plan

- First slice: WebSocket handshake version/key validation.
- Next: select feature/NFR option A, B, or C.
- Then: security lifecycle, visible browser UX, renderer evidence, docs, verify.

## SDN

```sdn
plan {
  first_slice = "ws_handshake_gate"
  selection_needed = ["feature_option", "nfr_option"]
  remaining = ["auth_lifecycle", "browser_ux", "external_renderer_evidence"]
}
```
