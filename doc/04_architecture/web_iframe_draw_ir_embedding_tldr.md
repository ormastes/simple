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
- Prohibit child `[u32]` buffers and iframe IMAGE shortcuts.
- Migrate four public pixel callers, then recursive child paint; delete old
  blit helpers only after exact parity.
