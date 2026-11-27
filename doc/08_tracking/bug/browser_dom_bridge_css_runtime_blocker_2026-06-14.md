# Browser DOM Bridge CSS Runtime Blocker - 2026-06-14
## Resolved 2026-11-25 — parser false positive fixed earlier; remaining API drift fixed and gated

- **measured** (2026-11-25, Windows x86_64, tracked `bin/simple.exe`, `SIMPLE_LIB=src ... run --mode=interpreter`):
  the 2026-09-13 load blocker is gone — the `namespace:` named-argument false
  positive no longer fires. Both parsers now guard it: pure-Simple
  `src/compiler/10.frontend/parser/recovery.spl:205` only flags
  `namespace <Identifier>`, and the seed
  `src/compiler_rust/parser/src/error_recovery.rs:508` has the same
  name-follows guard. `use app.ui.browser.dom_bridge.{DomBridge}` loads.
- **measured**: with the module loading, the real residual blocker surfaced —
  `dom_bridge.spl` was written against a removed API: `List<T>.new()`
  (`error: semantic: ... unknown class List`), `CSSValue`/`CSSDeclaration`
  (renamed to `RsCssValue`/`RsCssDeclaration` on 2026-08-19),
  `CSSRule.create`/`Selector.create` (gone), `Element.attributes` as
  `List<Attr>` (now `Dict<text, text>`), and `UIEvent.Click` (variant
  removed; its reference also forced a whole-module JIT demotion).
- **fixed 2026-11-25**: `src/app/ui.browser/dom_bridge.spl` ported to the
  current APIs — `Dict<text, text>` attributes, `RsCss*` types,
  struct-literal `CSSRule(selectors: [...], declarations: ...)`,
  `UIEvent.MouseEvent` for click/mousedown — and the `parse_css_rules`
  repeated tail-slice loop replaced with the position-index scan this doc's
  Next Step called for.
- **measured** (after): probe run prints `rules: 2 / elements: 1 / texts: 1 /
  rules-in-tree: 2`; a 400-rule stylesheet parses in **2106 µs** and a
  200-rule sheet in **682 µs** (previously a five-rule probe hung > 90 s);
  no JIT demotion remains. A 26-assertion mirror of the new spec passes
  `ALL CHECKS PASSED`.
- **gate added**: `test/01_unit/app/ui.browser/dom_bridge_css_spec.spl` — the
  CSS-parser-only focused executable test this doc asked for (rule counts,
  selector/declaration content, empty input, 200-rule regression guard,
  html_to_dom attributes/nesting).
- **host limit stated**: the spec harness (`bin/simple test`, `run <spec>`,
  `lint`) cannot execute on this host today — the tracked seed binary
  (2026-11-17) predates today's seed fix `14a34acbe1e` ("accept
  @representation_boundary as directive attribute"), so every closure that
  touches a decorated `nogc_sync_mut` module dies with
  `unknown decorator @representation_boundary` before any assertion runs.
  The spec's assertions were therefore executed via an equivalent
  `run`-mode probe (output above); the spec itself needs one CI run on a
  current binary.

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

