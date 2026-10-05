# JIT: two `WindowInfo` structs in one flattened unit drop the WM showcases to the interpreter

- **Filed:** 2026-10-05
- **Area:** the seed HIR struct registry (struct types are keyed by bare
  name) × `src/lib/common/ui/window.spl:9` and
  `src/lib/nogc_sync_mut/play/types.spl:173`
- **Status:** OPEN

## Symptom

At 3840x2160:

| entry | wall | RSS | mode |
|---|---|---|---|
| rendering_wm_core | 100.6 s | 4.17 GB | interpreted |
| rendering_wm_full | 182.9 s | 5.77 GB | interpreted |

Both render correctly, but slowly:

```
[jit-fallback] HIR lowering error: Cannot infer field type: struct 'WindowInfo'
field 'id' (declared fields: window_id, target_id, title, url, x, y, width,
height, focused) [in examples/06_io/ui/rendering/rendering_wm_core.spl]
```

## Root cause

Two unrelated structs named `WindowInfo` reach the same flattened unit:

| definition | fields |
|---|---|
| `src/lib/common/ui/window.spl:9` | `id, title, html, x, y, width, height` |
| `src/lib/nogc_sync_mut/play/types.spl:173` | `window_id, target_id, title, url, ...` |

HIR keeps one layout per bare struct name, so `info.id` in `common.ui.window`
is checked against the `play` layout. The duplicates in the `gc_async_mut` and
`nogc_async_mut` `play/types.spl` files and in `_McpOsServer/server_class.spl`
have the same shape.

Same defect class as
`duplicate_struct_decls_shadow_field_types_2026-08-10.md` (marked "LIKELY
RESOLVED" there) and `lint_dejits_whole_program_span_struct_collision_2026-08-18.md`
(OPEN). This is a live instance on current `origin/main`, so the class is not
resolved.

## Unblock

Register struct types by their owner (the flatten owner tag already used for
functions) instead of by bare name. Do not rename one of the structs to hide
this: any other same-named struct pair hits the same defect.

## Repro

```
SHOWCASE_RESOLUTION=4k SIMPLE_SHOWCASE_W=3840 SIMPLE_SHOWCASE_H=2160 \
SIMPLE_JIT_STRICT=1 <seed> run examples/06_io/ui/rendering/rendering_wm_core.spl
```
