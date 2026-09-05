# CSS gap zero cascade system-test plan

## Scope

Prove that a later valid `gap:0` resets an earlier positive Flex gap through
both canonical declaration application paths:

- dispatch path: inline `gap:0`;
- full Style reconstruction: inline `gap:0;visibility:visible`.

The production path is unchanged:

`HTML/CSS -> computed Style -> Web layout -> DrawIrComposition -> Engine2D`

No parser grammar, Web semantic schema, Draw IR schema, painter, Engine2D,
runtime, or compiler change is in scope. Malformed/negative values, percentage
gaps, multi-column `normal`, and broad CSS Box Alignment parity are excluded.

## Executable specification and manual

- `test/03_system/feature/web_platform/css/flex_gap_zero_cascade_spec.spl`
- `doc/06_spec/03_system/feature/web_platform/css/flex_gap_zero_cascade_spec.md`

The manual is hand-reviewed static documentation until qualified pure-Simple
execution and docgen are available; it does not claim runtime PASS.

## Frozen scenario flow

1. `Parse the split-cascade zero-gap fixture`
2. `Resolve zero-gap Web layout geometry`
3. `Emit adjacent canonical Draw IR rectangles`
4. `Render exact zero-gap Engine2D pixels`

## Acceptance oracles

- Both row styles expose `gap_px`, `row_gap_px`, and `column_gap_px` as zero.
- Dispatch row boxes are row `[0,0,12,2]`, red `[0,0,4,2]`, and blue
  `[4,0,4,2]`.
- Full-reconstruction row boxes are row `[0,2,12,2]`, red `[0,2,4,2]`, and
  blue `[4,2,4,2]`.
- Four canonical `rect` commands retain exact geometry and colors
  `0xFFDC2626`/`0xFF2563EB`.
- Engine2D skips zero commands and returns all 48 expected pixels: four red,
  four blue, and four white pixels on each of four rows.

## Traceability

| Requirement | Executable scenario | Oracle | Status |
|---|---|---|---|
| REQ-WEB-BROWSER-003 | `should reset positive Flex gaps through both declaration paths` | cascade style and exact layout | Static candidate |
| REQ-WEB-BROWSER-004 | same | canonical Draw IR and exact Engine2D pixels | Static candidate |
| REQ-WEB-BROWSER-021 | same | modern four-step SSpec plus mirrored manual | Static candidate |

## Verification policy

This implementation session is explicitly static-only. Do not bootstrap, run
the SSpec, or invoke docgen. One static check set validates diff hygiene,
fixture/step/manual parity, shared owner use, placeholder absence, and zero
executable specs under `doc/06_spec`.
