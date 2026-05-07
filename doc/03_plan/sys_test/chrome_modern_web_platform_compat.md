# Chrome Modern Web Platform Compatibility System Test Plan

Date: 2026-05-06

## Scope

This system test plan covers the acceptance tests for `doc/03_plan/chrome_modern_web_platform_compat_plan.md`.

In scope:

- Plan completeness for current Chrome-era HTML/CSS/JS compatibility work.
- BDD/SSpec traceability for the initial implementation slice.
- Verification gates for WPT-subset, Test262-subset, and pixel comparison work.
- Explicit handling of unsupported or partial compatibility claims.

Out of scope:

- Claiming full Chrome compatibility.
- Importing the complete WPT or Test262 suites.
- Implementing all missing HTML, CSS, DOM, or JavaScript features.

## Test Environment

- Repository root: `/home/ormastes/dev/pub/simple`
- Test runner: `bin/simple test`
- Primary SSpec: `doc/06_spec/app/lib/feature/chrome_modern_web_platform_compat_spec.spl`
- Focused renderer SSpec: `test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl`

## Traceability Matrix

| Requirement | Description | Test File | Test Cases | Coverage |
| --- | --- | --- | --- | --- |
| REQ-001 | Compatibility matrix | `chrome_modern_web_platform_compat_spec.spl` | 3 | Full |
| REQ-002 | WPT subset path | `chrome_modern_web_platform_compat_spec.spl`, `selector_color_subset_spec.spl` | 4 | Full |
| REQ-003 | Test262 subset path | `chrome_modern_web_platform_compat_spec.spl` | 3 | Full |
| REQ-004 | Supported feature evidence | `chrome_modern_web_platform_compat_spec.spl` | 5 | Full |
| REQ-005 | Unsupported feature tracking | `chrome_modern_web_platform_compat_spec.spl` | 3 | Full |
| REQ-006 | Verification gate | `chrome_modern_web_platform_compat_spec.spl` | 3 | Full |
| REQ-007 | Initial modern CSS BDD slice | `chrome_modern_web_platform_compat_spec.spl`, `browser_renderer_spec.spl` | 4 | Full |

## BDD Scenarios

REQ-001: Compatibility Matrix

- Given the plan exists, when it is inspected, then it should require HTML, CSS, DOM/rendering, and JavaScript matrix coverage.
- Given the matrix requirement, when statuses are inspected, then it should require `supported`, `partial`, `missing`, and `not-applicable`.
- Given the matrix exit gate, when migration readiness is inspected, then it should require selecting first WPT/Test262 subsets.

REQ-002: WPT Subset Path

- Given browser compatibility depends on WPT, when the plan is inspected, then it should create a WPT subset path.
- Given the first WPT subset path, when artifacts are inspected, then it should provide an executable selector/color SSpec.
- Given WPT migration, when the initial subset is inspected, then it should cover CSS selectors, CSS colors, HTML parser basics, and rendering basics.
- Given WPT execution, when the exit gate is inspected, then it should require at least 25 WPT-derived SSpec cases.

REQ-003: Test262 Subset Path

- Given JavaScript compatibility depends on Test262, when the plan is inspected, then it should create a Test262 subset path.
- Given Test262 migration, when classification is inspected, then it should require expected-pass, expected-fail, and unsupported-host states.
- Given Test262 execution, when the exit gate is inspected, then it should require at least 50 stable Test262-derived cases.

REQ-004: Supported Feature Evidence

- Given a feature is marked supported, when evidence is inspected, then it should require SSpec or external-suite mapping.
- Given the current modern CSS slice, when renderer SSpec is inspected, then it should include `:is()` coverage.
- Given the current modern CSS slice, when renderer SSpec is inspected, then it should include `:where()` coverage.
- Given the current modern CSS slice, when renderer SSpec is inspected, then it should include positive and negative `:not()` coverage.
- Given the current modern CSS slice, when renderer SSpec is inspected, then it should include positive and negative simple descendant `:has()` coverage, plus bounded direct-child `:has(> .class)` coverage.
- Given the current modern CSS slice, when renderer SSpec is inspected, then it should include positive and negative partial `:empty` coverage.
- Given the current modern CSS slice, when renderer SSpec is inspected, then it should include positive and negative partial `:first-child` coverage.
- Given the current modern CSS slice, when renderer SSpec is inspected, then it should include positive and negative partial `:last-child` coverage.
- Given the current modern CSS slice, when renderer SSpec is inspected, then it should include positive and negative partial `:only-child` coverage.
- Given the current modern CSS slice, when renderer SSpec is inspected, then it should include simple rule extraction from nested CSS `@layer` blocks.
- Given the current modern CSS slice, when renderer SSpec is inspected, then it should include bounded simple `&` parent-selector CSS nesting coverage.
- Given the current modern CSS slice, when renderer SSpec is inspected, then it should include basic attribute presence and exact-value selector coverage.
- Given the current modern CSS slice, when renderer SSpec is inspected, then it should include prefix, substring, and whitespace-token attribute selector operator coverage.
- Given the current modern CSS slice, when renderer SSpec is inspected, then it should include dash-match attribute selector operator coverage.
- Given the current modern CSS slice, when renderer SSpec is inspected, then it should include ASCII case-insensitive attribute selector flag coverage.
- Given the current modern CSS slice, when renderer SSpec is inspected, then it should include explicit case-sensitive attribute selector flag coverage.

REQ-005: Unsupported Feature Tracking

- Given full Chrome compatibility is not complete, when the report is inspected, then it should explicitly say Simple is not full Chrome-compatible.
- Given unsupported features, when the plan is inspected, then it should require owner-ready gap tracking with priority and acceptance criteria.
- Given unsupported high-value areas, when the report is inspected, then it should list WPT, Test262, HTML semantics, and CSS layout gaps.

REQ-006: Verification Gate

- Given compatibility verification, when gates are inspected, then PASS/WARN/FAIL states should be defined.
- Given local verification, when commands are inspected, then `bin/simple check src/lib` should be required.
- Given no manual-only success, when criteria are inspected, then visual inspection should not be the only signal.

REQ-007: Initial Modern CSS BDD Slice

- Given modern CSS selector-list pseudos, when source is inspected, then `:is()` and `:where()` matching should be implemented.
- Given modern CSS selector-list pseudos, when source is inspected, then partial `:not()`, descendant `:has()`, and bounded direct-child `:has(> ...)` matching should be implemented.
- Given modern CSS structural pseudos, when source is inspected, then partial `:empty` matching should be implemented for empty element content.
- Given modern CSS structural pseudos, when source is inspected, then partial `:first-child` matching should be implemented for first element content.
- Given modern CSS structural pseudos, when source is inspected, then partial `:last-child` matching should be implemented for last element content.
- Given modern CSS structural pseudos, when source is inspected, then partial `:only-child` matching should be implemented for sole element content.
- Given modern CSS at-rules, when source is inspected, then simple CSS `@layer` wrappers should be flattened before existing rule scans.
- Given modern CSS selectors, when source is inspected, then simple `&` parent-selector nested rules should be flattened before existing rule scans.
- Given modern CSS selectors, when source is inspected, then basic `[attr]` and `[attr=value]` matching should be implemented.
- Given modern CSS selectors, when source is inspected, then bounded `[attr^=value]`, `[attr*=value]`, and `[attr~=value]` matching should be implemented.
- Given modern CSS selectors, when source is inspected, then bounded `[attr|=value]` matching should be implemented for exact-or-hyphen language style values.
- Given modern CSS selectors, when source is inspected, then bounded `[attr=value i]` matching should be implemented with the unflagged path remaining case-sensitive.
- Given modern CSS selectors, when source is inspected, then bounded `[attr=value s]` syntax should be accepted and remain case-sensitive.
- Given fallback renderer extraction, when source is inspected, then commas inside functional selectors should not split selector lists.
- Given BDD coverage, when renderer SSpec is run, then the `:is()`, `:where()`, `:not()`, simple descendant/direct-child `:has()`, simple CSS `@layer`, simple CSS nesting, attribute selector/operator, `:empty`, `:first-child`, `:last-child`, and `:only-child` examples should pass.

## Execution Order

1. Run the plan acceptance SSpec.
2. Run the WPT selector/color subset SSpec.
3. Run the focused browser renderer SSpec.
4. Run `bin/simple check src/lib` after implementation changes.

## Pass/Fail Criteria

PASS:

- The plan acceptance SSpec passes.
- The WPT selector/color subset SSpec passes.
- The focused renderer SSpec passes.
- `bin/simple check src/lib` passes.

WARN:

- The plan and focused slice pass, but broad WPT/Test262 import remains incomplete and documented.

FAIL:

- Any supported feature lacks test evidence.
- Any unsupported high-value feature is unclassified.
- Any required verification command fails.
