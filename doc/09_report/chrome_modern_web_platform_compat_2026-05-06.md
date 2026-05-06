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

Coverage lives in:

- `test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl`

## Implementation Added

Implemented modern selector-list pseudo matching for:

- Style-block DOM matching in `src/lib/gc_async_mut/gpu/browser_engine/style_block.spl`
- Fallback pixel renderer style-block extraction in `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl`

The fallback CSS scanner now avoids splitting commas inside functional selector pseudos.

## Remaining Gaps

- No complete WPT migration yet. A practical next step is a small fixture importer for selected WPT CSS selector/rendering cases.
- No complete Test262 migration yet. A practical next step is a Simple-compatible Test262 subset runner for parser-only and interpreter-supported ES2025 cases.
- HTML modern element semantics such as popover, dialog modal behavior, inert, declarative shadow DOM, and full form validation are not claimed.
- CSS modern layout systems such as container queries, subgrid, cascade layers, and nesting are not claimed complete.
