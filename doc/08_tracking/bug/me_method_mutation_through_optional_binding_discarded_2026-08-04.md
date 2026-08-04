# `me`-method mutation through an OPTION-typed binding is silently discarded

**Date:** 2026-08-04
**Status:** OPEN (language/runtime defect). Callers must work around it by
destructuring; the workaround is applied in `engine2d/engine.spl`.
**Severity:** High — silent, exit 0, no warning, no lint. Every state change a
mutating method makes is thrown away.

## Symptom

Calling a `me` (mutating) method on a binding whose static type is `T?` mutates a
temporary unwrap that is then discarded. The binding — and anything re-wrapped
from it — keeps the pre-call value. Calling the *same* method on a binding
produced by `if val Some(x) = opt:` writes back correctly.

## Minimal reproducer

`optwb_probe.spl` (scratchpad), `SIMPLE_EXECUTION_MODE=interpreter bin/simple run`:

```
class Counter:
    var n: i64 = 0
    me bump():
        self.n = self.n + 1

# Arm A -- optional-typed binding
var oa: Counter? = Some(Counter(n: 0))
val a = oa
if a == nil:
    print("A nil")
else:
    val ca = a          # ca : Counter?  <-- the defect
    ca.bump()
    ca.bump()
    oa = Some(ca)

# Arm B -- destructured Some binding
var ob: Counter? = Some(Counter(n: 0))
if val Some(cb) = ob:
    cb.bump()
    cb.bump()
    ob = Some(cb)
```

Observed:

```
A n=0     <-- both mutations lost
B n=2
C n=2     (C = same as B with a nested `me` call; nesting is fine)
```

Expected `A n=2`. The call is accepted with no error and no warning; nothing in
`lint` flags it.

## Why it matters

This is not a toy. It silently broke the Vulkan engine2d run lane for weeks —
see `run_lane_render_truncation_divergence_2026-08-02.md`. The font route was
written as

```
val active = self.vulkan_backend        # VulkanBackend?
if active == nil: ...
else:
    val vulkan = active                 # still VulkanBackend?
    var evidence = vulkan.composite_font_batch(x, y, batch)
    self.vulkan_backend = Some(vulkan)  # re-wraps the UNMUTATED value
```

so the entry flush inside `composite_font_batch` — which submits and clears the
pending compute batch — never reached the backend the engine kept. The stored
backend went on re-submitting an already-consumed command buffer, returning
`rc=-1` for every later flush and primitive dispatch, and the failure flags set
on the discarded copy never reached the readback, which published a truncated
frame as a proven `device_readback`.

## The two idioms are visually near-identical

`val x = <optional>` and `if val Some(x) = <optional>` differ by six characters
and read the same; only the second writes back. In `engine2d/engine.spl` both
appeared in the same `for target in plan:` loop, one per backend.

## Remaining occurrences of the losing idiom

`val active = self.<optional>` followed by `val y = active` and a mutating call:

| file:line | binding | mutating call | status |
|-----------|---------|---------------|--------|
| engine2d/engine.spl:282 | vulkan | `install_font_atlas_pipeline` | FIXED 2026-08-04 |
| engine2d/engine.spl:~1455 | vulkan | `composite_font_batch` | FIXED 2026-08-04 |
| engine2d/engine.spl:~2353 | vulkan | `draw_image_blend_checked` | FIXED 2026-08-04 |
| engine2d/engine.spl:292 | cuda | `install_font_atlas_ptx` | OPEN |
| engine2d/engine.spl:527 | metal | (font install) | OPEN |
| engine2d/engine.spl:~1421/1434/1445/1488 | cuda/metal/opencl/rocm | `draw_font_batch` | OPEN |
| engine2d/engine.spl:~2363 | metal | `draw_image_blend_checked` | OPEN |
| engine3d/engine.spl:91,190,207,215,355,414 | `_font_renderer` / `_vulkan_font` | various | OPEN |

`engine2d/engine.spl:498` uses the same idiom but only *reads*
(`parent.owns_session`), so it is unaffected.

The non-vulkan rows are left open deliberately: none of those backends
initialize on this host, so a change to them could not be verified here, and an
unverified edit to a GPU dispatch path is worse than a filed defect.

## Fix direction

1. **Language/compiler (real fix).** Either reject a `me`-method call on an
   optional-typed receiver at type-check time (forcing `.?` or a destructure),
   or make the implicit unwrap write the mutated value back through the
   binding. Silent acceptance is the defect.
2. **Lint backstop (cheap, do this regardless).** A rule that flags a mutating
   method call whose receiver's static type is `T?` would have caught every row
   in the table above at authoring time.
