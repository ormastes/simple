---
id: browser_script_crossmodule_mutation_breaks_timer_event_2026-07-11
status: OPEN
severity: medium
discovered: 2026-07-11
discovered_by: browser script API conformance probes (tools/pixel_compare/probe_xmod.spl, probe_bind.spl)
related: src/lib/gc_async_mut/gpu/browser_engine/script/timer_api.spl
related: src/lib/gc_async_mut/gpu/browser_engine/script/event_api.spl
related: src/lib/gc_async_mut/gpu/browser_engine/script/event_loop.spl
---

# Cross-module class-arg mutation is lost under the seed interpreter — blocks setTimeout/addEventListener persistence

**Status:** OPEN. Interpreter/codegen limitation (the documented "class-arg
in-place mutation is unreliable cross-module" landmine). Blocks the browser
timer + event-listener APIs whose signatures cannot adopt the return-value
workaround.

## Summary

A `pub fn` in module A that mutates a class/collection argument (either by
direct field write or by calling a `me` method) does **not** persist the
mutation back to the caller in module B under the seed interpreter (JIT rejects
it with `W1006: mutation without mut capability` and falls back to an interpreter
that copies the argument by value).

Two workarounds exist and were applied where signatures allowed:
- **return-value**: `x = f(x)` — used for storage/console/dom mutators.
- **`mut` param**: `f(mut x)` — requires the caller pass a `var`.

`set_timeout(loop, id, ms) -> i64` and `node_add_event_listener(node, …)` can
use neither cleanly: `set_timeout`'s return slot is the timer id (cannot also
return the loop), and the specs call the event/timer functions in **statement
position on `val` bindings** (so `mut` is a compile error and there is no
reassignment to receive a returned value). The mutation is therefore lost.

## Minimal repro

```
# probe_xmod.spl — cross-module mutator, effect lost
var s = BrowserStorage.new()
storage_set_item(s, "k", "v")     # (pre-fix void signature)
storage_get_item(s, "k")          # => nil  (mutation did not persist)
# JIT: "W1006: mutation without mut capability ... while lowering storage_set_item"
```

```
# probe_bind.spl — direct me-call persists (I), cross-module fn does not (J)
var p2 = BeDomNode.element("div"); p2.add_child(BeDomNode.element("span"))
var ex2 = p2.children[0]
ex2.set_attr("k", "v")            # PASS (direct me-call)
node_set_attribute(ex2, "k", "v") # (pre-fix) FAIL (cross-module fn param)
```

Observed failures: `timer_api_spec` (fires/repeats/rAF register — 8 failed),
`event_api_spec` (adds/capture listener — 2 failed).

## Expected

Cross-module mutation of a class/collection argument via a `me` method or field
write persists to the caller (matching the compiled-binary semantics), so
`set_timeout`/`addEventListener` register on the caller's live loop/node.

## Related value-copy limitation (DOM handles)

`BeDomNode` is a value type and `document_get_element_by_id` /
`document_query_selector` return a value-copy extracted from the tree. Even
with the return-value mutator convention, `n = node_set_attribute(n, …)` mutates
the copy — a subsequent **re-query of the tree does not observe the change**.
The single most common real-page idiom,
`document.getElementById('x').innerHTML = …`, therefore cannot be made to
persist to the live tree through the current handle-based API. A durable fix
needs reference-typed DOM nodes (dom.spl) or a mutate-in-place-by-id API
(`document_set_*_by_id(root, id, …) -> BeDomNode`). The conformance matrix's
mutation rows all use build-then-query or same-`var` reassignment, which work;
mutate-then-requery does not.
