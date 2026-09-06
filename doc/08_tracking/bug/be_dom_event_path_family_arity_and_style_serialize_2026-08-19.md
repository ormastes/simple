# be_dom path-event family broken by ctor arity; serialize drops <style> text

Status: OPEN P2. Filed 2026-08-19 (found by the chrome counter component harness,
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
