# Web showcase `vector-font-evidence`: CSS style pass truncates on wall-clock budget, marker node keeps default style

**Date:** 2026-08-01
**Status:** ROOT-CAUSED (fix plan below; not yet landed)
**Severity:** HIGH — sole blocker for showcase web cell #3; also a fail-open
evidence channel (a truncated render reports plausible-but-wrong font evidence)
**Gate:** `examples/06_io/ui/web_render_file_gui.spl`,
`run_web_standards_showcase()` fail-branch 5 of 6 (`return 10`)

## Symptom

```
web_standards_showcase status=fail reason=vector-font-evidence
expected_identity=sha256=c4f5361ce120af3e6b9156d0bf379fa19cda2ea0cd18ac01fd99596c6bf66e3f;axes=static
identity=sha256=a3041811a78c361b1de50f953c805e0244951c21c5bd412f7232ef0d899af0da;axes=wght=100
expected_pixels=100 pixels=16
```

Two wrongnesses in one verdict — a different font face, and the CSS-default
`font-size: 16` where `100` is required. They have **one** root cause.

## Root cause

`compute_styles_with_material()`
(`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl:2555`)
guards its per-node cascade loop with a wall-clock budget and **`break`s** on
expiry. Nodes not yet reached keep `renderer_default_style()` — i.e.
`font-family: sans-serif`, `font-size: 16`.

The verdict-producing run tripped exactly that guard (verbatim, from the same
run that emitted the `status=fail` line above):

```
[web-style-producer] budget-break at=74 of=151 now_us=2539458642 deadline_us=2520000006
```

The showcase's evidence marker is injected by `web_live_evidence_html()`
immediately before `</body>`, so it is **node 149 of 151** — the last element in
the document. Any budget break at all drops it. The marker therefore never
receives `font-family: Bungee; font-size: 100px`; it keeps the default style.

Both reported values follow mechanically from that one truncation:

1. **Wrong identity.** The marker keeps `sans-serif`, which
   `browser_font_candidates_for_family()` maps to the bundled default face
   `assets/fonts/google-fonts/ofl/notosanssc/NotoSansSC[wght].ttf` — candidate
   index 0, **Noto Sans SC**, whose identity is exactly the observed
   `sha256=a3041811…;axes=wght=100`.
2. **`pixels=16`.** `_simple_web_draw_ir_last_text_font_pixel_size()`
   (`simple_web_layout_engine2d_fast.spl:157`) returns the `font-size` of the
   **last** text command whose `font-identity` equals the render's identity.
   With the marker gone, every surviving text command is default body text at
   16 px carrying that same default identity, so the scan returns 16.

### The resolver itself is CORRECT — proved, not inferred

Isolated probe through the existing `font_renderer_debug_resolve` entry point
(`src/compiler_rust/target/bootstrap/simple run`, cwd = repo root):

```
bundled_path=assets/fonts/google-fonts/ofl/bungee/Bungee-Regular.ttf
cand_count=1
cand=assets/fonts/google-fonts/ofl/bungee/Bungee-Regular.ttf ident=sha256=c4f5361ce120af3e6b9156d0bf379fa19cda2ea0cd18ac01fd99596c6bf66e3f;axes=static
resolve100=valid=true family=Bungee identity=sha256=c4f5361ce120af3e6b9156d0bf379fa19cda2ea0cd18ac01fd99596c6bf66e3f;axes=static reason=resolved
resolve16=valid=true family=Noto Sans SC identity=sha256=a3041811a78c361b1de50f953c805e0244951c21c5bd412f7232ef0d899af0da;axes=wght=100 reason=resolved
```

`Bungee @ 100` resolves to the pinned expected identity. The observed wrong
identity is precisely what `sans-serif @ 16` resolves to. Font selection,
`browser_bundled_font_path_for_family`, and the pinned catalog are all fine —
nothing downstream of the cascade is at fault.

An interpreter-lane run that did **not** trip the budget completed the pass and
styled the marker correctly:

```
[font-inline-trace] index=149 post_inline_apply_font_family=Bungee post_inline_apply_font_size=100
[font-inherit-trace] index=149 final_font_family=Bungee final_font_size=100
[font-style-trace] index=150 font_family=Bungee font_size=100 language=en text=Simple Web 300 DPI
```

This is engine-independent: the failure follows the budget break, not the lane.

## Why the style pass is too slow (the thing to actually fix)

The pass spends its whole budget re-parsing the same font file once per text
node. From the verdict run's own `[rfm]` receipts:

| receipt | count |
|---|---|
| `at=measure` (full measurement performed) | 30 |
| `at=cache-hit` (resolved-metrics cache served) | **0** |
| `at=renderer-bound from_cache=true` | 28 |

`from_cache=true` does **not** mean a parsed face was reused.
`_browser_default_for_family_cached()`
(`src/lib/nogc_sync_mut/text_layout/font_renderer.spl:408`) caches only a flat
**text path**; on a hit it calls `_browser_default_font_rebuild_from_path()`,
which constructs a fresh `FontRenderer` and calls
`try_load_selected_bytes(path, blob)` → `FontRasterizer.load_selected_bytes(...)`
— a **full TrueType parse of the 17.7 MB `NotoSansSC[wght].ttf` blob, per text
node**. Thirty text nodes is roughly half a gigabyte of redundant font parsing
inside a 10 s budget.

The path-only flattening was deliberate (see the `FLATTENED` comment above
`_browser_default_font_families`) because a module-global array of nested
`FontRenderer` object graphs was not trusted to persist. That workaround is what
now costs the budget.

## Secondary defect: the degradation signal is fail-open

`simple_web_layout_last_render_degraded()`
(`simple_web_html_layout_renderer_foundation.spl:169`) is set to `true` on a
budget break — and has **zero consumers repo-wide**. So a render whose cascade
was truncated still reports `vector_font_identity` / `vector_font_pixel_size` as
if they were complete evidence. The gate then compares a fabricated value
against the pinned one and reports a font mismatch, which points investigation
at font selection instead of at the truncation. Three prior sessions were sent
down that path.

Independently of the perf fix, a budget-truncated render must not be able to
emit vector-font evidence at all: it should fail closed with a distinguishable
reason (e.g. `reason=vector-font-evidence-degraded`) so the truncation is named
at the point it happens.

## Fix plan

1. **Cache the parsed face, not the path** (removes the blocker). Keep the
   already-constructed `FontRenderer`/`FontRasterizer` for a resolved path in a
   module-global slot so consecutive resolutions of the same family reuse one
   parsed face instead of re-parsing the blob. A single-entry (last-path) cache
   already eliminates ~28 of the 30 re-parses on this page, since the document
   is overwhelmingly one family. Verify against the `FLATTENED` comment's
   concern before widening it to an array.
2. **Make the degraded flag load-bearing** (removes the misdirection). Thread
   `simple_web_layout_last_render_degraded()` into the
   `SimpleWebLayoutEngine2DExecutionResult` vector-font fields and fail closed
   on it. This is a strengthening — it never relaxes the pinned identity or the
   `expected_pixels=100` requirement.
3. Do **not** raise `WEB_RENDER_BUDGET_MS` or relax the gate. The budget is a
   real timeout and the pinned identity is the evidence; fitting either to the
   observed value would hide the defect.

## UPDATE 2026-08-01: item 2 landed; item 1 is MEASURED INSUFFICIENT

**Item 2 (fail closed) is done** — `render_degraded` is threaded onto
`SimpleWebLayoutEngine2DExecutionResult` / `SimpleWebLayoutEngine2DReadbackResult`
and through `SimpleWebEngine2DStaticPixelCache`, and the showcase gate now fails
`reason=vector-font-evidence-degraded` (exit 12) BEFORE any font comparison.

**Item 1 will not produce a green cell.** It is a real improvement but the gap
is an order of magnitude larger than a face cache can close. Measured with
`src/compiler_rust/target/bootstrap/simple run`, interpreter lane, via
`font_renderer_debug_resolve`:

| what | measured |
|---|---|
| resolve, **distinct** content per call (steady state) | **~2.45 s per text node** |
| first (cold) resolve | 9.7 s |
| `load_selected_font_file` on the 17.7 MB face (native `rt_file_hash_sha256` path) | 799 ms |
| `font_runtime_ttf_default_supported` | 9 ms |
| `browser_font_candidates_for_family` | 18 ms |

`WEB_RENDER_BUDGET_MS` is 10 000 and is stage-partitioned, so the style pass
gets a fraction of it. At ~2.45 s per distinct text node the budget is gone
after the first two or three text nodes — consistent with the observed
`budget-break at=74 of=151`. Roughly 30 distinct text nodes cost ~74 s. Removing
the per-node 799 ms file re-read saves at most about a third of that; the
remainder is interpreted shaping/measuring. Cell #3 is compiled-lane gated and
that lane is slower still, so the shortfall is ~10-30x, not ~2x.

**Measurement trap that cost this lane an hour, recorded so it is not repeated:**
resolving the *same* content repeatedly reports ~70 ms per call and looks like a
healthy cache. That is the resolved-metrics cache
(`_resolved_font_metric_cached`), whose key includes `content`, short-circuiting
before any font work. A real page has ~30 *distinct* strings, so it never hits
that cache. Any per-node cost measurement MUST vary the content. For the same
reason the `at=cache-hit` x0 receipt is **correct behaviour**, not a cache
defect — 30 distinct strings can only miss.

Note also that the two `[rfm]` receipt families describe *different* caches:
`from_cache=true` x28 is the FACE cache working, while `at=cache-hit` x0 is the
metrics cache correctly missing. Reading them as one cache is what produced the
"cache hit re-parses the blob per text node" framing above.

So the remaining blocker is the cost of an interpreted per-node text measure,
not font-face caching. Next lane should target that, and should not expect item
1 alone to flip the verdict.

## Repro

```bash
cd <repo>
SIMPLE_TIMEOUT_SECONDS=5400 SIMPLE_TRACE_FONT_STYLE=1 SIMPLE_WEB_PHASE_TRACE=1 \
  src/compiler_rust/target/bootstrap/simple run examples/06_io/ui/web_render_file_gui.spl
```

`SIMPLE_TIMEOUT_SECONDS` is required: the seed applies its own 10 s watchdog to
any path containing `examples/`
(`src/compiler_rust/driver/src/cli/examples_safety.rs:12`), which otherwise
kills the run before a verdict. `SIMPLE_TRACE_FONT_STYLE=1` arms the
`[font-inherit-trace]` / `[font-style-trace]` / `[draw-ir-font-trace]` receipts;
`[web-style-producer] budget-break` is unconditional.

## Notes for the next session

- Fail-branches 1–4 (`wrong-pixel-count`, `initial-checksum-mismatch`,
  `blank-or-uniform`, `backend-provenance`) pass and are the regression controls.
- `draw_ir_style_props_pairing` (`..._paint_layout.spl:1148`) emitting **zero**
  lines while `[draw-ir-font-trace]` emits several is the signature of this bug:
  no node carrying `Bungee` ever reaches paint, because the cascade stopped
  before styling it. It is not evidence that the paint-side producer is wrong.
- `bin/simple` is stale/broken; use `src/compiler_rust/target/bootstrap/simple`.
