# DrawIR style diff linearization evidence — 2026-08-11

Status: PASS.

DrawIR diff and incremental patch generation previously carried two copies of
an order-independent O(P²) computed-style comparison for every matched
command. Both now use one shared comparison:

- normal producer output with unique property keys: O(P) dictionary lookup;
- malformed duplicate-key input: exact legacy nested-membership fallback;
- order-independent equality and prior asymmetric duplicate behavior retained.

This affects the canonical composition path shared by WebRenderer, GUI, and
WM. It does not change DrawIR or patch schemas.

Verification:

- `draw_ir_diff_spec.spl`: 5/5 PASS, including reordered styles, changed value,
  and duplicate-key sabotage.
- `draw_ir_patch_spec.spl`: 13/13 PASS, including all operation kinds, damage
  bounds, glyph payloads, stale revisions, and mixed 30-command round-trip.

This is an algorithmic hot-path improvement, not an 8K/80 throughput claim.

## Damage amplification follow-up

Patch generation now emits damage once per changed component rather than once
per narrow operation. A component changing geometry, style, and text retains
all three patch operations but contributes only its old/new bounds, reducing
six duplicate rectangles to two and avoiding false rectangle-cap/full-frame
fallbacks. The expanded patch suite passes 14/14 with an exact multi-field
mutation and round-trip oracle.

Identical old/new bounds are also collapsed. In-place style, text, color, or
glyph changes now contribute one rectangle rather than two; moves and resizes
still contribute both old and new bounds. The 14/14 suite passes with glyph
payload sabotage and distinct move-bound assertions.

## Full-command hardening

Incremental patch detection and its round-trip oracle now cover every
`DrawIrCommand` field. Previously omitted clip/content/hit/border rectangles,
image URI, advance widths, edge payload, and points now use the existing
full-command update carrier and emit damage. Zero-size path/edge commands
derive conservative half-open damage bounds from their points. A sabotage
fixture changing only clip, image URI, path points, and advances passes, and
the complete patch suite is 15/15 PASS.

The sibling baseline diff classifier now uses exact full-command equality as
well, so clip/image/path/advance-only changes cannot be mislabeled unchanged.
Its expanded suite is 6/6 PASS.
