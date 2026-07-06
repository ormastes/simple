# Interpreter: `Dict<K, ClassInstance>.get()`/`.set()` copies the value — mutations through the fetched instance are silently lost

- Date: 2026-07-06
- Severity: high (silent state loss — any cache/accumulator held in a Dict misbehaves)
- Found during: task #15 S1 cache wiring (WebRenderPixelArtifactCache in HostCompositor)

## Symptom
Fetching a class instance from a `Dict` and mutating it does NOT persist: the next `.get()`
returns the pre-mutation state. Hit/store counters and last-rendered-content fields on a
cache object stored in `HostCompositor.content_caches: Dict<window_id, WebRenderPixelArtifactCache>`
were silently reset every frame.

## Root cause direction
Interpreter `Dict` get/set copy class values instead of sharing the reference (same family
as the known "Value::Dict deep-clones on cache hits" memory note and the earlier
`self.x.arr.push()` non-persistence landmine).

## Workaround (in tree, at both call sites in host_compositor_entry.spl)
Explicitly write the mutated instance back into the dict after each use:
`caches.set(id, cache)` following mutation — documented inline. Verified empirically (n=3):
nested mutation + write-back persists; without write-back it does not.

## Fix direction
Make interpreter Dict value access share references for class instances (align with class
reference semantics elsewhere), or document + lint the copy semantics. Add a regression
spec: mutate-through-get persists without manual write-back.

## Repro sketch
1. `var d: Dict<i64, C> = {}` with `class C: n: i64`
2. `d.set(1, C(n: 0))`; `val c = d.get(1)`; `c.n = 5`
3. `d.get(1).n` → expected 5, observed 0.
