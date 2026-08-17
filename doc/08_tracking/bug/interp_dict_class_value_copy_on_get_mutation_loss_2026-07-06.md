# Interpreter: `Dict<K, ClassInstance>.get()`/`.set()` copies the value — mutations through the fetched instance are silently lost

> **Family root cause — see
> `interp_list_class_element_read_returns_copy_mutation_loss_2026-08-17.md`**,
> the canonical record for class-value identity in the interpreter (list index /
> field bind / dict get). This record keeps its own symptom, repro and history in
> full; it is cross-referenced, not superseded. Its CLOSED verdict is unchanged —
> it rests on two independent execution re-measurements and was not re-litigated
> by source reading. Note that the underlying engine defect (source `class`
> values are the copy-on-write `Value::Object` carrier; `Value::ClassInstance` has
> zero producers, verified 2026-08-17) is **still open** — this surface is masked
> by path-based write-back, not fixed, so the `caches.set(...)` write-backs in
> `host_compositor_entry.spl` should stay until option A in the canonical record
> lands.

Status: CLOSED — NOT REPRODUCED 2026-08-17 (P1). Independently re-confirmed by EXECUTION; see the two 2026-08-17 sections below.

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


## Re-measurement 2026-08-17 (P0-core silent-wrong triage lane) — NOT REPRODUCED

Binary: `bin/release/x86_64-unknown-linux-gnu/simple`, 59,536,728 bytes, mtime
2026-08-16 22:59:37 UTC (Rust seed). Probes run under both
`SIMPLE_EXECUTION_MODE=interpreter` and `=jit`.

The filed "Repro sketch" was executed verbatim:

```
class C:
    var n: i64
var d: Dict<i64, C> = {}
d.set(1, C(n: 0))
val c = d.get(1)
c.n = 5
print d.get(1).n
```

Prints `5` on BOTH engines (the doc's expected value); the reported observation
was `0`. Mutation through a `Dict`-fetched class instance now persists without
the manual `caches.set(id, cache)` write-back the doc describes as the in-tree
workaround.

**Scope of this close.** This disproves the defect on the two Rust-seed engines
only, which is where it was originally observed (interpreter). It says nothing
about the pure-Simple self-hosted interpreter — no self-hosted binary is
deployed in this tree (`bin/simple` is the seed), so that lane could not be
measured. It also does not re-verify the two original `host_compositor_entry.spl`
call sites; the workaround write-backs there are now believed redundant but
were NOT removed or re-tested, so do not treat this as authority to delete them
without re-measuring that path.


---

# 2026-08-17 — independent second re-measurement (CRITICAL lane) — CONFIRMS NOT REPRODUCED

Independent of the triage-lane re-measurement above, re-run on
`bin/release/x86_64-unknown-linux-gnu/simple` (59,536,728 bytes, mtime
2026-08-16 22:59:37, Rust seed). The doc's own "Repro sketch" verbatim:

```
class C:
    var n: i64

fn main():
    var d: Dict<i64, C> = {}
    d.set(1, C(n: 0))
    val c = d.get(1)
    c.n = 5
    print(d.get(1).n.to_text())
```

```
$ bin/simple run repro.spl                                 -> 5
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run repro.spl -> 5
```

Expected 5, observed 5, on both engines. The filed observation was `0`.
Mutation through a `Dict`-fetched class instance persists with no manual
`caches.set(id, cache)` write-back.

Verdict rests on **EXECUTION**, not source reading. Consistent with the
`merge_shared_collection_fields` COW write-back work already in-tree
(`interpreter_call/core/function_exec.rs`).

**Not proven:** the native/AOT (`native-build`) lane was not exercised, and the
original `HostCompositor.content_caches` call site was not re-run in situ. The
`caches.set(...)` write-back workaround is still present in
`host_compositor_entry.spl` and was not removed.
