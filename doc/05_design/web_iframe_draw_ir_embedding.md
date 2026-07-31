<!-- codex-design -->
# Detail design: Web iframe Draw IR embedding

Architecture: `doc/04_architecture/web_iframe_draw_ir_embedding.md`

## Minimal source changes

1. `src/lib/common/ui/draw_ir.spl`: add `draw_ir_embed_composition` and one
   private command copy-with-clip helper; reuse existing rect operations.
2. `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`:
   extract `_simple_web_layout_compose_document`; extend retained composition
   with depth/deadline; segment commands and insert children in paint order.
3. `simple_web_html_layout_renderer_paint_layout.spl`: retain pixel helpers
   during parity; delete them only after all five callers migrate.
4. Add `test/02_integration/rendering/simple_web_iframe_draw_ir_embedding_spec.spl`
   and its mirrored zero-stub manual.

No Engine2D change is planned. A required executor change means the flat
transform contract was implemented incorrectly.

## Producer algorithm

Keep aligned `commands/command_owner_nodes` from `_html_draw_ir_commands`.

1. Build `last_command_by_owner`.
2. Append commands in paint order to the current parent segment.
3. After an iframe owner's final command, flush the segment; compute its
   border/padding content rect and intersection with
   `paint_clip_at(ancestor_clip_cache, iframe_index)`.
4. Hidden/empty intersection: emit nothing. Failed depth/deadline/group
   admission: emit clipped placeholder. Otherwise compose the child and append
   `draw_ir_embed_composition(...)`; append its already-nested material witness
   to the ordered child-witness list at the same point.
5. Continue later siblings and flush the tail.

Segment IDs are `html-layout` plus a monotonic segment index. Iframe prefixes
use `_html_draw_ir_component_id` plus depth. Add no hash/cache key.

The existing fractional-opacity partition remains unchanged without iframes.
An iframe inside it is a fail-closed placeholder for this tranche.

After segmentation, `_simple_web_layout_merge_material_witness` folds the
parent witness followed by child witnesses in insertion order. It sums CPU and
solid counts separately and hashes the architecture's framed
`count:sha256` sequence only for multiple nonzero contributors. Raw
entries/counts/node arrays stay parent-document local for retained rerender;
child node indices are never rebased. The combined witness supplies final
provenance and backend execution checks.

## Deadline

```text
remaining = parent_deadline_us - now_us
child_deadline = now_us + remaining / 2
```

If remaining is non-positive, emit placeholder. Otherwise save the current
deadline, install the child deadline, compose, and restore. No retry or sleep.

## Modern SSpec TDD matrix

Frozen displayed steps:

- `Compose iframe srcdoc through Web semantics and Draw IR`
- `Preserve iframe paint order and ancestor clipping`
- `Bound nested iframe work and fail closed`
- `Retire legacy iframe pixel blitting after parity`

| Scenario | Semantic/layout | Draw IR | Engine2D/pixels | Control |
|---|---|---|---|---|
| basic `srcdoc` | replaced iframe, fallback absent, exact content box | child `html_ast` batches, stable prefixed IDs, zero iframe IMAGE commands | child color only inside box | parent marker/outside unchanged |
| later overlapping sibling | source paint order | child batches precede later sibling | sibling wins overlap | reversed order reverses winner |
| overflow/negative origin | exact ancestor/content intersection | every child command has present local clip | zero child color outside intersection | unclipped count is larger |
| nested depth 2 | two decoded child documents | accumulated rebased origins | deepest unique color visible | no image resource |
| depth 4 | fourth child not parsed | one capped placeholder | placeholder; deepest color zero | depth 3 renders |
| expired deadline | no child parse/layout | placeholder only | bounded deterministic output | live deadline renders |
| separate/shared CSS | parent style absent/present | exact child style metadata | unique color absent/present | child own declaration wins |
| empty `srcdoc`/fallback | fallback hidden | empty child canvas, no fallback commands | white child | fallback color zero |
| external `src` | no resource authority | no external command | deterministic empty child | ledger unchanged |
| fractional ancestor | unsupported group | placeholder, no independent-alpha child batches | fail-closed pixels | opaque renders |
| child material | child material stays document-local | combined count/framed hash follows child insertion order; no transient IR fields | provenance matches Engine2D material execution | parent-only hash is byte-identical |
| retained scroll | stable IDs, shifted box once | no duplicate offset; clip shifts | fresh/retained checksum equal | zero-scroll baseline |
| five caller parity | identical semantic/layout input | canonical composition source | exact supported-corpus pixels/checksum | mismatch blocks migration |

Use only canonical matchers. The manual shows the first three flows and folds
matrix cases. Initial missing helpers call `fail(...)`; never `pass_todo` or a
constant assertion.

## Caller migration order

Run each focused parity gate once.

1. `simple_web_layout_render_html_software_pixels_traced`
2. `simple_web_layout_render_html_software_result`
3. `simple_web_layout_render_html_gpu_frame` (solid-only shortcut remains only
   when no iframe exists)
4. `simple_web_layout_render_html_software_pixels_at_scroll`
5. `_web_render_child_pixels` recursion

Then delete `_web_blit_child`, `_web_render_child_pixels`, and
`_web_paint_iframes`; point the old iframe spec/manual to the canonical suite
instead of maintaining duplicate behavior tests.

## Verification boundary

Use a qualified pure-Simple stage 2/3 or release binary for focused spec and
docgen. No full bootstrap, Rust seed, or renderer-wide suite. Static review
alone remains RED.
