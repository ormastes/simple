# be_dom path-event family broken by ctor arity; serialize drops <style> text

Status: FIXED 2026-11-09 (p3-browser sweep, seed interpreter evidence).
Ctor-arity half fixed by 2dfaae16e88 (ancestor of release/1.0.0); the
<style>-serialize half had regressed on release/1.0.0 and was re-landed in
the same sweep (html_tree_builder.spl gives <style> a real element + raw
text child again). Verified: be_dom_event_path_and_style_serialize_spec
2/2 PASS. Filed 2026-08-19 (found by the chrome counter component harness,
tools/component_diff/CONTRACT.md).

1. `be_dom_create_event` (src/lib/gc_async_mut/web/dom_accessors.spl ~615) calls
   `BeDomEvent.create` with 7 args against a 4-param signature — the whole
   path-based `be_dom_dispatch_event_path` family fails at runtime ("unknown
   static method create"). The typed-route family works and is what the
   harness (and browser session) use. Fix the arity or delete the dead family.
2. `be_dom_serialize_html` drops `<style>` element text content, so mutated
   DOM states re-layout against the pristine fixture's static CSS instead of
   the serialized document's.

Repro: tools/component_diff/run_component_diff.shs (see CONTRACT.md).
