# `mut Engine3D` free-function call silently drops mutation once 6+ sibling args are dynamic

- **Status:** OPEN
- **Discovered:** 2026-07-11 (Lane D: `model3d` 3D node-in-node nesting, `test/02_integration/app/model3d/model3d_nested_nodes_spec.spl`)
- **Area:** compiler codegen — argument marshalling/register allocation for a free
  function whose first parameter is `mut <ClassType>` (a "handle" class holding
  interpreter/JIT-visible mutable state), combined with several other
  parameters
- **Severity:** High — silently drops ALL geometry from a render, with zero
  error, warning, or crash. The framebuffer still clears to the correct
  background color (so a naive smoke test can look "almost right"), but no
  triangle ever rasterizes. Easy to miss without an explicit non-background
  pixel assertion.
- **Likely related:** `struct_param_mutation_semantics_2026-07-03.md` and
  `browser_engine_free_fn_arg_mutation_lost_2026-06-30.md` document a
  different-shaped but same-family bug (class-instance-argument mutation lost
  across a free-function boundary under the compiled/JIT backend). This bug
  is triggered purely by **argument dynamism/count**, not by an argument
  being class-typed — see isolation below.

## Symptom

`src/app/model3d/main.spl`'s `render_scene` composed a scene's node tree,
extracted per-box `(cx, cy, cz, sx, sy, sz, col)` from parsed/computed scene
data, and called a free-function helper:

```spl
fn _submit_box(mut e: Engine3D, cx: f32, cy: f32, cz: f32, sx: f32, sy: f32, sz: f32, col: u32):
    ...
    e.submit_triangle(...)   # x10, inside this function
```

Every `_submit_box(e, cx[i], cy[i], cz[i], sx[i], sy[i], sz[i], col[i])` call
executed without error, but `e.read_pixels()` afterward showed ONLY the
background clear color — every submitted triangle was silently absent from
the framebuffer. `e.clear(...)`/`e.clear_depth()` (called directly in
`render_scene`, not through a free-function wrapper) worked correctly the
whole time, which is what made this easy to misdiagnose as a
`Scene3`/`Node3` class-mutation bug rather than an argument-count issue.

## Isolated repro (exhaustive A/B, all in a throwaway module — files deleted after use)

Held constant across every variant: identical box-submission math (10
`e.submit_triangle(vertex3d_pos_normal(...), ..., mat, m)` calls per box),
identical camera setup, identical 96×72 framebuffer, identical expected
center-pixel color. Only the **shape of the call into the `mut Engine3D`
free function** varied:

| Variant | Result |
|---|---|
| `fn f(mut e: Engine3D, cx: f32, ...)` called with **compile-time literal** args (`f(e, 0.0, 0.0, 0.0, 1.0, 1.0, 1.0, 0xFFCC3020)`) | **WORKS** |
| Same signature, called with args read from arrays/fields (dynamic) — 5 dynamic + 2 literal fallback args | **WORKS** |
| Same, 6 dynamic + 1 literal | **BROKEN** |
| Same, all 7 dynamic | **BROKEN** |
| 7 dynamic values **pre-bound to individual `val` locals** before the call (not inlined in the call's argument list) | **BROKEN** — proves it isn't about the call-site expression shape |
| 6 dynamic values **packed into a single `[f32]` array argument** + 1 more (2 total arguments to the callee, still 6 dynamic values in scope) | **BROKEN** — proves it isn't about argument *count* to the callee either |
| Same, using an array **slice** (`arr[0:6]`) instead of 6 separate `arr[i]` reads | **BROKEN** — proves it isn't about the read syntax |
| `f64`-typed scalar params instead of `f32` (everything else equal) | Also **BROKEN independently** (an f64-vs-f32 confound found and ruled out mid-investigation — f32 alone is necessary but not sufficient) |
| **Same 6–7 dynamic values, same math, but `e.submit_triangle(...)` called directly as a METHOD on the local `e`** (no free-function wrapper — `e` is never passed positionally into another function) | **WORKS**, regardless of how many dynamic values feed the inlined corner computation |

Net: the bug is specific to **free functions with an explicit `mut <ClassType>` parameter**, invoked with **6 or more sibling arguments that are not compiler-visible constants** (array reads, computed locals, slices — literal/`val`-constant folding seems to be what keeps the good cases safe). Calling methods directly on the mutable handle (`e.method(...)`) instead of threading it through another free function sidesteps the bug entirely, with no upper bound on argument dynamism observed in that shape.

## Current workaround (landed)

`src/app/model3d/main.spl`: removed the `_submit_box(mut e: Engine3D, ...)`
free-function helper entirely; the box-drawing math (corner computation +
10 `e.submit_triangle(...)` method calls) is now inlined directly into
`render_scene`'s loop body, reading `cx[i]`/`cy[i]`/.../`col[i]` from plain
`[f32]`/`[u32]` arrays. See the docstring on `render_scene` in that file for
the in-code pointer back to this doc.

## Follow-up

- Root-cause in the compiler/JIT backend (likely `src/compiler_rust/compiler/**`
  argument-passing/register-allocation for calls with a `mut`-capability class
  parameter) is out of scope for this pass — no compiler changes were made,
  per the "don't touch the compiler/seed for feature work, workaround in pure
  Simple" project convention.
- Worth a dedicated minimal repro script kept under a bug-report/regression
  directory once triaged, to make this a permanent regression check for
  whichever team member picks up the compiler fix. Not added here to avoid
  growing the model3d app's test surface with a compiler-internals-only file.
- Should be cross-referenced against `struct_param_mutation_semantics_2026-07-03.md`'s
  "Recommendation" section once someone starts the compiled-backend
  argument-passing fix for `mut`-capability class parameters — these may
  share a root cause (both are about `mut <ClassType>` parameter handling in
  compiled/JIT free-function calls), just triggered along different axes
  (argument dynamism/count here vs. a second class-typed argument there).
