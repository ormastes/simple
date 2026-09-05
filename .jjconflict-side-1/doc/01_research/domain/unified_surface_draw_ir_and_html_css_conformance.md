<!-- codex-research -->
# Domain Research — Rendering IR and Web Conformance

Date: 2026-07-29
Status: research complete

## Standards findings

- The WHATWG HTML parser defines tree construction for `text/html`; tag
  inventory alone does not prove parser conformance:
  https://html.spec.whatwg.org/multipage/parsing.html
- WHATWG HTML rendering is primarily expressed through expected default
  presentation and CSS behavior. HTML conformance therefore needs parser,
  DOM/semantics, default-style, interaction, and rendered evidence:
  https://html.spec.whatwg.org/multipage/rendering.html
- CSS separates declared, cascaded, computed, used, and actual values. A shared
  execution IR should receive used/actual paint facts rather than re-run the
  cascade:
  https://www.w3.org/TR/CSS21/cascade.html
- CSS partial implementations must reject an unsupported declaration as a
  declaration; they must not selectively apply supported components from an
  invalid multi-value declaration:
  https://www.w3.org/TR/css-cascade-6/
- Web Platform Tests use reftests as a primary rendering oracle. Tests wait for
  load/fonts/paint and can use `TestRendered` for post-load mutations:
  https://web-platform-tests.org/writing-tests/reftests.html
- WPT recommends JavaScript tests for APIs and rendering/reftests for graphical
  behavior:
  https://web-platform-tests.org/writing-tests/

## Architectural implications

1. Semantic IR and execution IR have different jobs. HTML/CSS, widgets, and
   terminal cells retain domain state until layout and style are resolved.
2. One execution display list prevents backend, serializer, diff, capture, and
   validation forks.
3. Conformance must be organized by specification behavior and WPT manifests,
   not raw counts of tags or property names.
4. Exact internal Simple comparisons are appropriate. Cross-browser raster
   comparisons need controlled fonts, device scale, viewport, color space, and
   explicit antialiasing tolerances.
5. Dynamic rendering tests must wait for the intended animation/mutation frame
   and then assert semantic state plus pixels; a timer firing alone is not
   rendering evidence.

## Recommended evidence hierarchy

1. Parser/DOM tree and error recovery.
2. Cascaded/computed/used style.
3. Layout boxes, line fragments, stacking and clips.
4. `DrawIrComposition` commands and provenance.
5. Engine2D exact pixels/readback.
6. WPT reference or pinned Chromium comparison.

Each lower level supplements rather than replaces the higher-level root-cause
oracle.

