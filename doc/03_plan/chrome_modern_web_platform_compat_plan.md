# Chrome Modern Web Platform Compatibility Plan

Date: 2026-05-06

## Goal

Bring Simple's browser-facing HTML, CSS, and JavaScript support from targeted compatibility toward measurable current-Chrome/web-platform compatibility.

This plan does not assume "fully Chrome-compatible" is a single implementation task. The success target is evidence-driven conformance against selected WPT and Test262 suites, with unsupported areas explicitly tracked.

## Current Baseline

- HTML: partial parser/rendering support. No full WHATWG HTML living-standard claim.
- CSS: partial parser/style/rendering support. Modern `:is()` and `:where()` selector-list support is now covered in SSpec for the browser renderer.
- JavaScript: partial ECMAScript support. No full ECMA-262 2025 or Test262 conformance claim.
- Compatibility suites: existing SSpec coverage exists, but no broad WPT or Test262 migration harness is complete.

## Standards And Test Sources

- HTML/CSS/DOM/browser behavior: Web Platform Tests (WPT).
- JavaScript language behavior: Test262 for ECMA-262.
- Practical web feature target: Baseline plus current Chrome feature status.
- Internal test format: SSpec.

## Success Criteria

1. A compatibility matrix exists for HTML, CSS, DOM/rendering, and JavaScript.
2. A repeatable WPT-subset import path exists for browser-facing tests.
3. A repeatable Test262-subset path exists for JavaScript parser/interpreter tests.
4. Every supported feature has SSpec coverage or an explicit external-suite mapping.
5. Every unsupported high-value feature has a tracked gap with owner, priority, and acceptance criteria.
6. Verification can report PASS/WARN/FAIL without relying on manual visual inspection.

## Acceptance Artifacts

- Feature requirements: `doc/02_requirements/feature/chrome_modern_web_platform_compat.md`
- NFR requirements: `doc/02_requirements/nfr/chrome_modern_web_platform_compat.md`
- System test plan and BDD scenarios: `doc/03_plan/sys_test/chrome_modern_web_platform_compat.md`
- Executable SSpec acceptance tests: `doc/06_spec/app/lib/feature/chrome_modern_web_platform_compat_spec.spl`

## Phase 1: Inventory And Compatibility Matrix

Create:

- `doc/09_report/web_platform_feature_matrix.md`
- `doc/09_report/ecmascript_feature_matrix.md`

Tasks:

- List currently supported HTML elements, attributes, parser behaviors, DOM behaviors, and rendering behaviors.
- List currently supported CSS selectors, cascade behavior, color syntax, units, layout, typography, media queries, and animations.
- List currently supported ECMAScript syntax, built-ins, runtime semantics, modules, async behavior, and host APIs.
- Mark each item as `supported`, `partial`, `missing`, or `not-applicable`.
- Add evidence links to local tests or source files.

Exit gate:

- Matrix documents exist and identify the first WPT/Test262 subset to migrate.

## Phase 2: WPT Subset Migration

Create:

- `tools/wpt_to_spipe/`
- `doc/03_plan/sys_test/wpt_subset_migration.md`
- `test/web_platform/`

Initial subset:

- CSS selectors: `:is`, `:where`, `:not`, `:has`, compound selectors, descendant/child combinators.
- CSS colors: hex, rgb, rgba, hsl, modern space-separated syntax, named colors, transparent/currentColor.
- HTML parser basics: document tree construction, implied elements, void elements, malformed nesting recovery.
- Rendering basics: block flow, inline text, margin/padding/border/background, flex basics.

Tasks:

- Build a small importer that converts selected WPT metadata and fixtures into SSpec-compatible fixtures.
- Keep imported cases curated and deterministic.
- Store original WPT source reference per migrated test.
- Avoid claiming full WPT conformance until broad automated coverage exists.

Exit gate:

- At least 25 selected WPT-derived cases run as SPipe and report deterministic PASS/WARN/FAIL.

## Phase 3: Test262 Subset Migration

Create:

- `tools/test262_to_spipe/`
- `doc/03_plan/sys_test/test262_subset_migration.md`
- `test/js/test262_subset/`

Initial subset:

- Parser syntax: `let`, `const`, arrow functions, template literals, optional chaining, nullish coalescing.
- Built-ins: `Array`, `String`, `Object`, `JSON`, `Promise` where already implemented.
- Runtime semantics: lexical scope, closures, strict equality, property access, exceptions.

Tasks:

- Build a Test262 harness adapter for Simple's JS engine.
- Support expected-pass, expected-fail, and unsupported-host classifications.
- Convert only cases that can run without unsupported browser/Node host APIs.
- Record all skipped features with reason.

Exit gate:

- At least 50 selected Test262-derived cases run with stable classification.

## Phase 4: High-Value Feature Implementation

Prioritized CSS:

- Selector specificity for `:is()` and zero-specificity `:where()`.
- `:not()` selector-list support.
- `@media` query basics for viewport width/height.
- CSS nesting parser support if local parser architecture can support it cleanly.
- Cascade layers only after specificity/order behavior is reliable.

Prioritized HTML:

- Modern semantic elements parsing/rendering fallback: `main`, `section`, `article`, `nav`, `header`, `footer`, `search`.
- `template` parsing behavior.
- `dialog` and `popover` tracked as later interactive features, not basic parser features.

Prioritized JavaScript:

- Close gaps found by the selected Test262 subset.
- Stabilize object literal/property behavior before broad built-in expansion.
- Add missing modern syntax only with parser and interpreter tests together.

Exit gate:

- Every implemented feature has focused SSpec plus source-suite traceability.

## Phase 5: Visual And Pixel Compatibility

Create:

- `doc/09_report/web_render_pixel_compat_matrix.md`
- `test/baselines/web_platform_subset/`

Tasks:

- Render each selected HTML/CSS fixture through Simple.
- Render equivalent fixture through Chrome when a Chrome harness is available.
- Compare non-background pixels, color buckets, layout extents, and deterministic signatures.
- Store start/final snapshots for JS-driven fixture cases.

Exit gate:

- Pixel comparison reports stable PASS/WARN/FAIL for every fixture.

## Phase 6: Verification Pipeline

Required commands:

- `bin/simple check src/lib`
- Focused browser renderer SSpec.
- WPT-subset SSpec.
- Test262-subset SSpec.
- Existing JS compatibility tests.

Final release gate:

- `STATUS: PASS` only when all required checks pass.
- `STATUS: WARN` if unsupported WPT/Test262 cases are classified and documented.
- `STATUS: FAIL` if supported features regress or unclassified failures remain.

## Risks

- Full Chrome compatibility is very large; without strict subset selection this can become unbounded.
- WPT and Test262 include host assumptions that may not map directly to Simple.
- Pixel comparison can be flaky unless fonts, viewport, device scale, and color conversion are pinned.
- Adding modern CSS semantics without full specificity/cascade support can produce misleading compatibility claims.

## Recommended Next Step

Start with Phase 1 and Phase 2 together:

1. Build the feature matrix.
2. Create the WPT selector/color subset.
3. Expand SSpec coverage from the newly supported `:is()` and `:where()` path into `:not()` and specificity/cascade behavior.
