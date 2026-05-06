# Chrome Modern Web Platform Compatibility Requirements

Date: 2026-05-06

## Scope

These requirements turn `doc/03_plan/chrome_modern_web_platform_compat_plan.md` into testable acceptance criteria. They cover the planning and test-design deliverables needed before broad implementation of Chrome/Web Platform compatibility.

## Requirements

REQ-001: Compatibility Matrix

The project shall maintain a documented compatibility matrix for HTML, CSS, DOM/rendering, and JavaScript that marks features as `supported`, `partial`, `missing`, or `not-applicable`.

REQ-002: WPT Subset Path

The project shall define a repeatable WPT-subset migration path for browser-facing HTML, CSS, DOM, and rendering behavior, including deterministic SSpec execution and source-suite traceability.

REQ-003: Test262 Subset Path

The project shall define a repeatable Test262-subset migration path for JavaScript parser and interpreter behavior, including expected-pass, expected-fail, and unsupported-host classification.

REQ-004: Supported Feature Evidence

Every feature that the project claims as supported shall have SSpec coverage or a traceable mapping to an external conformance-suite case.

REQ-005: Unsupported Feature Tracking

Every unsupported high-value feature shall be recorded with priority, acceptance criteria, and a clear unsupported/partial status rather than being silently treated as compatible.

REQ-006: Verification Gate

The compatibility workflow shall define PASS/WARN/FAIL verification gates that distinguish passing supported features, classified unsupported cases, and unclassified failures without relying on manual visual inspection as the only success signal.

REQ-007: Initial Modern CSS BDD Slice

The initial BDD slice shall cover modern CSS selector-list pseudo behavior for `:is()` and `:where()` in the Simple browser renderer.
