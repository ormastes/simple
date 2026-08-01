# Web iframe Draw IR embedding — TLDR

`<iframe srcdoc>` recurses through Web semantic/style/layout, flattens the
child `DrawIrComposition` at the iframe paint position, then renders once
through Engine2D.

- Reuse flat batch embedding plus command clips; add no new IR.
- Add `draw_ir_embed_composition(...)` in `common/ui/draw_ir.spl`.
- Preserve order/source/opacity; prefix IDs; intersect inherited clips.
- Fold document-local material witnesses parent-first, then child insertion
  order; keep transient entries/node indices out of Draw IR.
- Keep depth cap 3 and half-remaining-deadline admission.
- `space=shared` prepends parent rules; default `separate` does not.
- Keep `src`, opacity groups, navigation, JS sharing, and input routing RED.
- Prohibit child `[u32]` buffers and iframe IMAGE shortcuts on the retained
  path; the old pixel path remains only as the caller-migration oracle.
- Migrate four public pixel callers, then recursive child paint; delete old
  blit helpers only after exact parity.
- Before enabling child behavior, use typed parent-DOM/iframe-route/child-frame
  identity, `about:srcdoc` plus separate effective base, and typed `Origin`;
  process generation remains the outer SBR2 lifetime.
- Isolated authority lives only in `HostedBrowserRendererProcess`; the worker
  mirrors it. Outer SBR2 protects one hop, while `SBCI1`/one-use `SBCP1` scope
  one child intent. Direct `HostedWebContentSession` uses the shared broker and
  no SBR2 wire.
