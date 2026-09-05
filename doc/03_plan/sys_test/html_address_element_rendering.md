# HTML address element rendering system-test plan

## Scope

Close one visible row in the uncapped HTML Partial backlog: the selected
user-agent presentation of `<address>` as a block with italic typography.
Prove author override parity through:

- direct declaration dispatch: `font-style:normal`;
- full Style reconstruction: `font-style:normal;visibility:visible`.

The unchanged route is:

`HTML semantics -> Web style/layout -> WebIR -> DrawIrComposition -> Engine2D`

Only the shared tag-default/declaration owner changes. Address semantics beyond
normal tree identity, locale-specific styling, font discovery, layout, Draw IR,
and Engine2D changes are excluded.

## Frozen scenario flow

1. `Parse address as a semantic body child`
2. `Resolve address UA typography through both style paths`
3. `Emit absolute address Draw IR geometry`
4. `Rasterize address typography with exact pixel controls`

## Acceptance oracles

- `body > address` semantic parentage is retained.
- Selected style is block/italic; direct and full overrides are block/normal.
- Every target box is `[0,0,80,16]` and lowers to the canonical rectangle and
  text commands with exact tag, display, font-style, color, and text origins.
- The selected frame equals an explicit italic control; both override frames
  equal an explicit normal control and differ from selected.
- Pixel `(79,15)` is `0xFFFEF3C7`; pixel `(1,18)` is `0xFFFFFFFF`; Engine2D
  skips zero commands in every frame.

## Traceability

| Requirement | Scenario evidence | Status |
|---|---|---|
| REQ-WEB-BROWSER-002 | semantic identity plus selected UA block/italic style | Static candidate |
| REQ-WEB-BROWSER-003 | direct/full `font-style:normal` parity | Static candidate |
| REQ-WEB-BROWSER-004 | absolute Draw IR geometry and discriminating pixels | Static candidate |
| REQ-WEB-BROWSER-021 | exact four-step modern SSpec and complete mirror | Static candidate |

## Static verification boundary

No runner, bootstrap, docgen, or push is authorized. One static gate checks
the exact five-file scope, one production owner, step/manual parity, both path
fixtures, oracle presence, placeholder absence, diff hygiene, and zero
executable specs below `doc/06_spec`.
