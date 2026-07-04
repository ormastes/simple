# Browser DOM Bridge CSS Runtime Blocker - 2026-06-14

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
