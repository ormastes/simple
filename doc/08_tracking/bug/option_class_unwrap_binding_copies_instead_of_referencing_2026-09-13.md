# `if val x = opt_class_field:` unwrap binds a COPY of a class instance, not the same reference — mutation through it is silently lost

- Status: OPEN (2026-09-13)
- Area: Rust seed interpreter, `Option<T>` unwrap / pattern-bind semantics for class (reference) types
- Severity: P1 — silently drops mutation with no error, and the affected
  pattern (`if val x = some_optional_class_field:`) is pervasive in this tree

## Found while

Diagnosing a regression in `test/01_unit/lib/blink/paint_tree_walker_spec.spl`
(tracked separately in
`blink_specs_import_unimplemented_modules_2026-08-10.md`, which closed this
spec at 6/6 on 2026-08-17; it is now 4/6). Traced the failure to
`src/lib/skia/entity/canvas.spl`'s `draw_rect`/`record` chain: `SkCanvas.recorder`
is an `Option<SkPictureRecorder>`, and every draw method does
`if val rec = self.recorder: rec.record(op)`. `record()` mutates
`self.ops.push(op)` (an array field on a `class`, which is a reference type
per this language's own documented semantics), yet the op never shows up when
the picture is finalized.

## Minimal isolated repro (no Skia, no Option-of-array involved)

```simple
class Counter:
    n: i64

impl Counter:
    fn bump_self():
        self.n = self.n + 1

class Holder:
    counter: Option<Counter>

fn main():
    val counter = Counter(n: 0)
    val h = Holder(counter: Some(counter))
    if val c = h.counter:
        c.bump_self()
    if val c = h.counter:
        c.bump_self()
    if val c = h.counter:
        print("n={c.n}")
    else:
        print("none")
```

Expected `n=2` (mutating the SAME `Counter` instance twice through its class
reference, exactly the way `h.counter.bump_self()` without the `Option`
wrapper already correctly does — see the control probe below). Actual:
`n=0` — every `if val c = h.counter:` unwrap appears to hand out a fresh copy
that the previous mutation never touched.

## Control probe — the SAME mutation with NO `Option` wrapper works

```simple
class Holder2:
    counter: Counter

fn main():
    val counter = Counter(n: 0)
    val h = Holder2(counter: counter)
    h.counter.bump_self()
    h.counter.bump_self()
    print("h.counter.n={h.counter.n}")   # 2 -- correct
```

This isolates the defect specifically to the `Option<ClassType>` unwrap-bind
path (`if val x = opt_expr:`), not to class mutation in general, and not to
method dispatch in general.

## Binary

`bin/simple` -> `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
`Simple Language v1.0.0-rc.1` (Rust bootstrap seed), sha256 prefix `3d120a6f`,
interpreter execution mode (`SIMPLE_EXECUTION_MODE=interpreter`).

## Why this matters beyond one spec

The `if val x = optional_class_field:` pattern is used pervasively for
exactly this reason (checking-and-using an `Option`), including at least
~20 call sites in `src/lib/skia/entity/canvas.spl` alone (every `draw_*`
method's `if val rec = self.recorder:` guard). Any of them that expects the
unwrap to yield a live reference to a class instance for MUTATION (as opposed
to read-only use) is silently a no-op today. This is a distinct defect from
the already-tracked struct-by-value mutation family
(`spec_value_type_helper_mutates_copy_family_2026-08-10.md`) — here the
receiver IS declared `class` (reference type) at every level; the loss
happens specifically at the `Option` unwrap boundary.

## Scope note

Interpreter/language-semantics defect in the Rust seed, not `src/lib`/`src/app`
source — out of scope for a contained pure-Simple bugfix. Left OPEN.

## Next step for whoever picks this up

Narrow further: does `if let`/`if val` binding for `Option<T>` route through a
different code path than a bare class-typed parameter bind? Compare the
seed's pattern-match/binding lowering for `Option::Some(x)` destructuring
against a plain class parameter bind to find where the copy is introduced.
