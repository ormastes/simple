# Browser DOM Bridge CSS Runtime Blocker - 2026-06-14
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Summary

`src/app/ui.browser/dom_bridge.spl` checks successfully, but executable runtime
probes that call `DomBridge.html_to_dom(...)` or `DomBridge.parse_css_rules(...)`
do not currently provide a usable focused gate for CSS parser optimization.

## Evidence

During GUI startup optimization work, a direct probe of:

- `DomBridge.html_to_dom("<div class=\"item_0\">Hello</div>", css)`
- `DomBridge.parse_css_rules(css)`

hit runtime/JIT fallback failures around inferred `ANY` fields and
`List<T>()` construction in the DOM bridge CSS helpers. After a local experiment
replaced the `List<T>()` helpers with arrays, even a five-rule direct probe did
not complete within 90 seconds and had to be stopped.

## Impact

The bridge still contains a likely startup-performance issue:
`parse_css_rules` repeatedly slices the remaining CSS tail after every rule,
which can turn large startup style sheets into repeated allocation/copy work.
However, the current runtime blocker prevents a safe, measured parser patch from
being landed without a stronger executable gate.

## Next Step

Create a small CSS-parser-only executable test that can run without the
`html_to_dom` attribute path and without hanging. Then replace the repeated
tail-slice loop with a position-index scan, rerun baseline/patched probes, and
only land the optimization with matching rule/declaration counts.

## Triage 2026-09-13 — LEFT OPEN, with the blocker's cause identified

- **measured** (Rust seed `bin/simple` v1.0.0-rc.1, Windows): the module no longer even loads, so no CSS probe is possible. A 6-line file doing `use app.ui.browser.dom_bridge.{DomBridge}` then `DomBridge.parse_css_rules(".item_0 { color: red; }")` fails in 1 second with `error: Common mistake detected` at `src/app/ui.browser/dom_bridge.spl:119:89`, caret on `namespace: ""`, advising "Use 'mod' for modules instead of 'namespace'."
- **measured**: the culprit is the parser's context-free common-mistake recovery firing on `namespace` used as a NAMED ARGUMENT in `Element(node_id: nid, tag_name: tag_name, attributes: attrs, namespace: "")`. This is precisely the latent case predicted by `parser_interface_path_segment_false_positive_2026-06-12.md` — its "Adjacent latent cases" section names `const`, `function`, `namespace`, `template`, `this` as sharing the same no-context check, with only `interface` guarded. `namespace` has now been hit for real.
- **inferred**: the fix is the same shape as the `interface` guard — skip the TsNamespace arm when the token sits in a named-argument position (next lexeme `:` inside a call) — in `src/compiler/10.frontend/parser/recovery.spl` and `src/compiler_rust/parser/src/error_recovery.rs`. Both are off-limits to this session: a bootstrap is running concurrently, and `src/compiler_rust/**` must not be edited.
- **inferred**: the original report's `List<T>()`/inferred-`ANY` runtime fallbacks and the >90 s five-rule probe hang could not be re-tested at all, since load now fails first. The `parse_css_rules` repeated-tail-slice perf concern also stands unmeasured.
- Verdict: OPEN, and now with a concrete first step that is independent of the CSS work.

