# CSS outline zero cascade system-test plan

## Scope

Prove that a later valid `outline:0` suppresses an earlier positive outline
through both canonical declaration application paths:

- dispatch path: inline `outline:0`;
- full Style reconstruction: inline `outline:0;visibility:visible`.

The existing production route remains:

`HTML/CSS -> computed Style -> Web layout -> DrawIrComposition -> Engine2D`

No parser grammar, Web semantic schema, layout algorithm, Draw IR schema,
painter, Engine2D, runtime, or compiler change is in scope. Full outline
grammar, focus-ring policy, CSS-wide keywords, and non-pixel lengths are
excluded.

## Executable specification and manual

- `test/03_system/feature/web_platform/css/outline_zero_cascade_spec.spl`
- `doc/06_spec/03_system/feature/web_platform/css/outline_zero_cascade_spec.md`

The manual is hand-reviewed static documentation. Qualified pure-Simple
execution and docgen remain pending; no runtime PASS is claimed.

## Frozen scenario flow

1. `Parse the split-cascade outline-zero fixture`
2. `Resolve zero-width outline Web style and geometry`
3. `Emit canonical Draw IR without outline expansion`
4. `Render exact outline-zero Engine2D pixels`

## Acceptance oracles

- Dispatch and full-reconstruction styles both expose `outline_w == 0`.
- Layout boxes remain `[2,2,2,2]` and `[6,2,2,2]`; outlines do not affect
  layout geometry.
- Both canonical rectangle commands retain those boxes, blue
  `0xFF2563EB`, and computed `outline-width` equal to `0`.
- Engine2D skips zero commands and returns all 60 expected pixels: two 2-by-2
  blue squares on an otherwise white 10-by-6 framebuffer, with no red ring.

## Traceability

| Requirement | Executable scenario | Oracle | Status |
|---|---|---|---|
| REQ-WEB-BROWSER-003 | `should suppress earlier outlines through both declaration paths` | cascade style and exact geometry | Static candidate |
| REQ-WEB-BROWSER-004 | same | canonical Draw IR and exact Engine2D pixels | Static candidate |
| REQ-WEB-BROWSER-021 | same | modern four-step SSpec plus mirrored manual | Static candidate |

## Static verification policy

Do not bootstrap, run the SSpec, invoke docgen, or push. One static check set
validates staged diff hygiene, exact step/manual parity, shared declaration
owner use, placeholder absence, intended file scope, and zero executable specs
under `doc/06_spec`.
