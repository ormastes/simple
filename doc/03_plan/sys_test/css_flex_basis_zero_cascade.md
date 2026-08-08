# CSS flex-basis zero cascade system-test plan

## Scope

Prove that a later valid `flex-basis:0` clears an earlier positive integer-pixel
basis through both canonical declaration paths:

- direct dispatch: inline `flex-basis:0`;
- full Style reconstruction: inline `flex-basis:0;visibility:visible`.

The unchanged production route is:

`HTML/CSS -> Web style/layout -> WebIR -> DrawIrComposition -> Engine2D`

Only the shared declaration owner changes. Flex shorthand interactions,
intrinsic/content bases, CSS-wide keywords, non-pixel lengths, layout, Draw IR,
and backend changes are excluded.

## Frozen scenario flow

1. `Parse the split-cascade flex-basis-zero fixture`
2. `Resolve zero flex basis Web layout geometry`
3. `Emit canonical Draw IR rectangles from WebIR`
4. `Render exact flex-basis-zero Engine2D pixels`

## Acceptance oracles

- Both reset items expose `flex_basis_px == 0`.
- Both 10-by-2 Flex rows contain a 2-by-2 red reset item followed by a 2-by-2
  blue control, leaving six white pixels per scanline.
- Canonical rectangle commands retain the exact WebIR-derived boxes and colors.
- Engine2D skips zero commands and returns all 40 expected pixels.

## Traceability

| Requirement | Scenario | Evidence | Status |
|---|---|---|---|
| REQ-WEB-BROWSER-003 | `should clear positive Flex bases through both declaration paths` | computed style and exact Web layout | Static candidate |
| REQ-WEB-BROWSER-004 | same | canonical Draw IR and all Engine2D pixels | Static candidate |
| REQ-WEB-BROWSER-021 | same | modern four-step SSpec and mirrored manual | Static candidate |

## Static verification boundary

No runtime, bootstrap, docgen, or push is authorized. One static gate checks
diff hygiene, intended production scope, both path fixtures, exact step/manual
parity, placeholder absence, and zero executable specs under `doc/06_spec`.
