# Web fractional leaf producer

Manual companion to
`test/03_system/app/ui/feature/web_fractional_leaf_producer_spec.spl`.
Generated SPipe output awaits a trustworthy Simple runner.

## Fixture

Each bounded scene renders at 16 × 16. Its immediate containing block is a
transparent, untransformed relative parent with integer pixel geometry. The
absolute leaf has an opaque background, explicit `box-sizing:border-box`, and
four authored pixel lengths. The leaf ID is used to find its real producer
DrawIR command.

## Scenarios and expected evidence

| Scenario | Required result |
|---|---|
| Direct decimal leaf | Empty scene rejection; exact f64 `1.25, 2.5, 4.75, 3.125`; all four legacy integer fields zero |
| CSS class fast path with only `width`/`height`, full class rule with position/paint, and direct inline declarations | All resolve to the same f64 geometry; the fast class retains authored `width`/`height` tokens |
| Later same-property declaration | Winning `left=1.25px` replaces `left=0.5px` in provenance and geometry |
| Parent at integer `(3,4)` | Leaf resolves to f64 origin `(4.25,6.5)` |
| `0.5px` by `0.5px` leaf | Positive f64 extent is emitted despite zero legacy dimensions |
| SDN and UiIr transport | Decoded DrawIR and lowered UiIr retain each f64 coordinate exactly |
| Fractional ancestor or rotated leaf | Nonempty scene rejection and zero partial fractional commands |
| Otherwise admitted leaf with `filter:blur(3px)` | Nonempty scene rejection and zero batches, even if the parsed Style appears neutral |
| Leaf with authored `clip-path`, `mask`, or `mix-blend-mode` | Each property independently yields nonempty rejection and zero batches |
| Leaf with `display:list-item` | Nonempty rejection and zero batches; marker paint is outside the admitted slice |
| Stylesheet with `div::before` | Nonempty rejection and zero batches before unsupported pseudo-element paint is lost |
| External `<link rel='stylesheet' href='theme.css'>` | Nonempty scene rejection and zero batches; unavailable stylesheet effects cannot be omitted |
| `<style>@import url(theme.css);</style>` | Nonempty scene rejection and zero batches before imported declarations are ignored |
| Legacy CPU executor | Explicit fallback and skipped command with `fractional-geometry-unsupported` reason |

The source spec contains executable assertions for each result. This manual
records intended behavior; no runtime PASS is claimed until the spec executes
on a trustworthy Simple runtime. It does not assert physical GPU pixels.

Requirements: REQ-2D-002, REQ-2D-006.
