# Interpreter: `me` method called through a `Trait?`-typed module slot re-boxes the receiver per call, losing field mutations

**Date:** 2026-07-07
**Severity:** medium — silently drops state mutations on any object stored
behind a `Trait?`-typed module-level `var` and invoked via a trait-typed
call; found while wiring `_wm_background_image_provider:
BackgroundImageProvider?` in `src/lib/common/ui/window_scene.spl`.
**Status:** CLOSED 2026-08-01 — misdiagnosed. Real defect, but **seed-only**,
and **not** trait-, optional-, or module-slot-specific. See "2026-08-01
re-diagnosis" below. The pure-Simple interpreter (the product) has been
correct since #112 landed `29c2a91a030` on **2026-07-04, three days before
this report was filed**; regression guard added to
`test/01_unit/compiler/interp_object_store_ref_model_spec.spl`.

## Symptom

A `me` (mutating) trait method invoked through a module-level slot typed
`SomeTrait?` gets a **freshly re-boxed copy of the receiver on every call**
when the slot is *re-read* between calls, so field mutations made inside the
method body do not persist to the next call.

**Repro nuance — this is not simple bind-once-call-twice:**

- Binding the trait value into a local once and calling the mutating method
  twice on that SAME local binding works fine — mutations persist call to
  call.
- The bug only reproduces when each call independently **re-reads the
  module-level slot** (`_wm_background_image_provider.resolve(...)` where
  the global `var` is read fresh each time), e.g. three sequential calls each
  doing `if provider is Some(p): p.mutate(); a = p.field` yield `a=1 b=1 c=1`
  instead of the expected accumulating `a=1 b=2 c=3` — every call sees the
  object in its initial state, as if a fresh copy were unboxed from the
  `Some(...)` each time the slot is read.

## Why it matters

Any provider/strategy object registered once into a `Trait?`-typed module
slot and expected to accumulate state across calls (caches, counters,
content-hash memoization) will silently lose that state if the call site
re-reads the slot per invocation — which is the natural way to write such
code (`_provider.resolve(...)` inline, not `let p = _provider; p.resolve()`
held across calls). Same interpreter-representation family as the Dict-value-
copy-on-read class of bugs already tracked elsewhere (boxed/optional values
get copied rather than referenced on each unwrap).

## Workaround applied (established convention, reused here)

`background_image_provider.spl`'s content-hash cache and stale-serve state
live in **module-level `var`s** (mirroring the pre-existing
`_*_compositor_override_*` pattern already used elsewhere in the compositor
code for exactly this reason), not as fields on the provider object reached
through the `Trait?` slot. State mutated via module-level `var` assignment
persists correctly across calls; state mutated via `me` methods on the
trait-slot-held object does not.

## 2026-08-01 re-diagnosis (supersedes the analysis above)

Reproduced on the Rust seed's **interpreter**
(`SIMPLE_EXECUTION_MODE=interpreter src/compiler_rust/target/bootstrap/simple
run`): the three-call repro yields `a=1 b=1 c=1` as reported. The seed's
**JIT** cannot judge this shape at all — the trait form aborts on duck-typed
dispatch, and the trait-free form returns nonsense (every `Impl()` reads as
one shared object).

### Not ADR-004

ADR-004 is scoped to *indexed* access — a Dict index, or a tuple/struct field
of an indexed element. Nothing here is indexed. The contract for `class` is
the opposite: `doc/06_spec/feature/language/memory_spec.md:84-89` and
`doc/06_spec/feature/language/data_structures_spec.md:97-98` specify class
instances as **reference types** ("Assignment copies the reference, not the
data"). So this is a genuine contract violation, not expected value
semantics.

### The three specifics in the original report are all wrong

A trigger matrix (optional vs plain, trait- vs class-typed, module vs local)
shows the copy is at **bind**, universally — nothing to do with traits,
optionals, module slots, or "re-boxing per call":

| shape | result |
|---|---|
| `val b = a; a.bump()` → `b.n` | **0** (expected 1) |
| `val xs = [d]; d.bump()` → `xs[0].n` | **0** (expected 1) |
| optional slot, trait- **or** class-typed, module **or** local | **1 1** |
| any non-optional binding, re-read per call | 1 2 (ok) |
| bind optional once, call twice on that binding | 1 2 (ok) |

The non-optional cases "work" only because the mutation and the read go
through the same slot. The one shape that does alias is passing an instance
as a function argument. Prior art for the same universal defect:
`data_structures_spec_remaining_2_failures_2026-05-30.md` (closed by
weakening the test, not by fixing the engine).

### Root cause (seed only)

`src/compiler_rust/compiler/src/value.rs:1161` represents a class instance as
`Object { class, fields: Arc<HashMap<String, Value>> }` — an `Arc` with no
interior mutability — and
`src/compiler_rust/compiler/src/interpreter/place.rs:132,176-177` mutate via
`Arc::make_mut(fields)`. That is copy-on-write, i.e. value semantics: a write
through one holder forks the map and is invisible to every other holder.

### Why no fix here

The seed is bootstrap-only, and the product interpreter already implements
the correct model: `src/compiler/70.backend/backend_types.spl:218`
(`ObjectValue{class_name, handle}`) plus
`src/compiler/70.backend/backend/objects.spl` (`ObjectStore`, handle ==
record index), so copying a `Value.Object` copies only an `i64` handle and
all copies share one record. Repairing the seed's value model would be a
refactor of a bootstrap-only engine, against the pure-Simple-first rule.

## Next step (original, retained for history)

Find where a `Some(x)`-wrapped trait object is unwrapped at each `Optional`
slot read in the interpreter (likely the same Optional/Result value-copy
path implicated in
`interp_fs_class_statics_return_result_despite_optional_types_2026-07-07.md`)
and confirm whether the unwrap clones the boxed value instead of returning a
shared reference/handle. A minimal regression repro: module-level
`var slot: SomeTrait? = nil`; register an object with a mutable counter
field; call a `me`-mutating method through `slot` (re-reading the module var
each time, not a locally-held binding) 3× in sequence; assert the counter
accumulates rather than resetting.
