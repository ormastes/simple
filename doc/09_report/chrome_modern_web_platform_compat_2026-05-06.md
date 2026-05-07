# Chrome Modern Web Platform Compatibility Audit

Date: 2026-05-06

## Scope

This audit checks Simple's browser-facing renderer/parser/JS surfaces against the current Chrome-era web platform model:

- HTML is a living web platform surface rather than a numbered "HTML version".
- CSS is a modular feature set; Baseline is the practical compatibility target for cross-browser feature readiness.
- JavaScript is standardized as ECMAScript. The current published standard is ECMA-262, 16th edition, June 2025.

References:

- Baseline explains current interoperable web platform feature readiness: https://web.dev/baseline
- WPT is the cross-browser web platform conformance suite: https://web-platform-tests.org/
- ECMA-262 2025 defines ECMAScript 2025: https://ecma-international.org/publications-and-standards/standards/ecma-262/
- Test262 is the ECMAScript conformance suite: https://github.com/tc39/test262

## Compatibility Position

Simple is not a full Chrome-compatible browser engine. Full compatibility would require a broad WPT import for HTML/CSS/DOM behavior and a Test262 harness for ECMAScript. The existing codebase has targeted browser-rendering, CSS parsing, HTML parsing, and JavaScript-engine tests, but not full WPT/Test262 coverage.

## Migrated SSpec Coverage

The high-value focused compatibility slice migrated into SSpec is modern CSS selector-list pseudo support in the fallback browser renderer:

- `:is(section, .card)` selector-list matching
- `:where(section, .card)` selector-list matching
- `div:is(.card, .panel)` tag-qualified matching
- `div:not(.disabled, #archived)` selector-list exclusion matching
- `div:has(.badge)` descendant matching with comma-safe selector-list parsing
- Simplified DOM event registration, cancelation, propagation, default-action metadata, keyboard activation, id path dispatch, and basic mouse/pointer payload fields including modifier-key state
- Layout-coordinate hit testing through pointer-derived `mousedown`/`mouseup`/`click` dispatch

Coverage lives in:

- `test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl`
- `test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.spl`
- `test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_hit_test_events_spec.spl`

## Implementation Added

Implemented modern selector-list pseudo matching for:

- Style-block DOM matching in `src/lib/gc_async_mut/gpu/browser_engine/style_block.spl`
- Fallback pixel renderer style-block extraction in `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl`
- Browser-engine DOM listener storage, deterministic capture/target/bubble dispatch, default-action metadata, and basic pointer event payload fields with modifier keys in `src/lib/gc_async_mut/gpu/browser_engine/dom.spl`
- Browser-engine layout hit-test event routing, coordinate/button/modifier payload propagation, and same-target pointer click synthesis in `src/lib/gc_async_mut/gpu/browser_engine/layout.spl`

The fallback CSS scanner now avoids splitting commas inside functional selector pseudos. `:not()` and `:has()` support is intentionally partial: it covers simple selector-list exclusion, descendant selector-list matching, and bounded direct-child `:has(> .class/tag/#id)` matching, and does not claim broader relative selectors, sibling combinators, specificity parity, or WPT completeness.
CSS nesting support is also intentionally partial: bounded simple `&` parent-selector rules are flattened before existing rule scans, but nested at-rules, selector-list specificity adjustment, relative selectors without `&`, media/container interactions, and full CSS Nesting Module parity are not claimed.
Structural pseudo support is still bounded: `:nth-child()` now covers numeric, `odd`, `even`, and common `an+b` arguments in the current style scanner/fallback renderer, but arbitrary formula parsing, `of <selector>` filters, generated content, comments, shadow DOM, and full Selectors Level 4 parity are not claimed.
Attribute selector support now includes exact quoted values with spaces and bounded suffix matching through `[attr$=value]` alongside exact, prefix, substring, token, dash, and ASCII case-flag paths; full escaping, namespaces, non-ASCII folding, and selector specificity parity are still not claimed.
Child combinator support now includes bounded fallback pixel matching for direct `body > div/.class/#id` rules with nested descendant rejection; arbitrary ancestor chains, DOM style-block parity, and specificity parity are still not claimed.
Adjacent sibling support now includes bounded fallback pixel matching for adjacent direct body-child `div` siblings with class/id-qualified previous and current selector forms and non-adjacent rejection; arbitrary parent sibling matching, non-`div` target rendering, DOM style-block parity, and specificity parity are still not claimed.
General sibling support now includes bounded fallback pixel matching for preceding direct body-child siblings against `div` targets with class/id-qualified previous and current selector forms and preceding-source rejection; arbitrary parent sibling matching, non-`div` target rendering, DOM style-block parity, and specificity parity are still not claimed.

## Remaining Gaps

- No complete WPT migration yet. A practical next step is a small fixture importer for selected WPT CSS selector/rendering cases.
- No complete Test262 migration yet. A practical next step is a Simple-compatible Test262 subset runner for parser-only and interpreter-supported ES2025 cases.
- HTML modern element semantics such as popover, dialog modal behavior, inert, declarative shadow DOM, and full form validation are not claimed.
- DOM Events support is still partial: no executable JavaScript callbacks, composed/shadow paths, retargeting, trusted events, async event-loop delivery, pointer capture, pressure/tilt/tangential pointer data, related targets, or full `MouseEvent`/`PointerEvent` parity are claimed.
- CSS modern layout systems such as container queries, subgrid, cascade layers, and nesting are not claimed complete; bounded simple `&` parent-selector nesting is covered only as flat-rule normalization.
