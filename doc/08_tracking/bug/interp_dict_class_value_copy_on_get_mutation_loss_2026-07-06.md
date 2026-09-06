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

## Re-probed 2026-09-06 — REPRODUCED, NOT FIXED

Binary probed: `bin/release/aarch64-unknown-linux-gnu/simple` (Rust seed,
aarch64). Both engines exercised: `SIMPLE_EXECUTION_MODE=interpret` (tree-walk)
and `env -u SIMPLE_EXECUTION_MODE` (default Cranelift JIT). Probe sources are
listed with each entry; they were run on both lanes and compared.

Still live on the interpreter, exactly as the record's repro sketch predicts:

```
DICT_MUT=0        # expected 1
```

after `d["a"] = Counter(n: 0)`, `d.get("a").unwrap().bump()`, re-`get`. Probe
`_scratch/p_cls.spl`. (The JIT lane could not be compared on the same probe: it
stops earlier on an unrelated `Option<ClassInstance>` receiver-resolution defect
— `.is_some()` on a `Dict.get()` result of class type binds as
`Counter.is_some`. That is noted in
`doc/08_tracking/bug/jit_is_some_is_none_method_dispatch_gap_2026-08-17.md`
under "Still open, adjacent".)

**Deliberately not fixed here, and why.** The value representation already has
the right carrier: `Value::ClassInstance(Arc<ClassInstance>)` shares identity,
while `Value::Object { fields: Arc<HashMap<..>> }` is copy-on-write and is what
class values actually use. Switching classes onto `ClassInstance` is not a local
edit — `compiler/src/value.rs:1756-1765` records that neither primary resolution
path has a `ClassInstance` arm (field access in `interpreter/expr/calls.rs` and
method dispatch in `interpreter_method/mod.rs` both match only `Value::Object`),
so flipping the constructor without adding both arms plus an audit of every
remaining `Value::Object` site would trade silent state loss for silent
resolution failure. That is a semantics change with its own verification pass,
not a bug fix to fold into an unrelated session.
