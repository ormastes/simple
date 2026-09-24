# Web catalog cold render profile, macOS M4 (2026-09-12)

Binary `build/cargo-r2/release/simple`, `stat -f '%z %m'` = `39368072 1789171430`,
identical before and after every run. `SIMPLE_EXECUTION_MODE=interpreter
SIMPLE_TIMEOUT_SECONDS=0`, one at a time, load average 3.0. Run from the worktree
`.claude/worktrees/agent-a4d142a4a64eed143`, whose `src/lib` is the edited tree —
proven, not assumed: the probe resolves `web_document_cache_hit`, a symbol that
exists only there. Probes under `build/perf/f11/` (gitignored).

## Cold render, `examples/06_io/ui/web_catalog/css-layout.html`

40,960 bytes, **908 DOM nodes**, 900x760, `cpu_simd`, `SIMPLE_WEB_PHASE_TRACE=1`.

| stage | ms | of cold frame | of pipeline |
|---|---|---|---|
| HTML parse | 611 | 0.2% | 2% |
| **style cascade** | **25,229** | **9.6%** | **86%** |
| layout | 651 | 0.2% | 2% |
| Draw IR build (compose/shaping) | 2,959 | 1.1% | 10% |
| document pipeline total | 29,451 | 11.2% | 100% |
| paint/raster (remainder) | 234,185 | 88.8% | — |
| **cold frame total** | **263,636** | | |

27.8 ms of style cascade per node against 0.67 ms of parse per node.

## Steady frames on the same real page (the F11 cache)

| frame | total ms | pipeline ms | cache_hit |
|---|---|---|---|
| 0 (cold) | 263,636 | 29,451 | false |
| 1 | 217,707 | 0 | true |
| 2 | 216,513 | 0 | true |
| 3 | 215,567 | 0 | true |

`hits=3 misses=1`. The whole 29.5 s pipeline disappears on a hit — **17% of the
steady frame**, entirely from not recomputing an unchanged document.

## Top 5 leaf loops, cold

| # | file:line | ms | class |
|---|---|---|---|
| 1 | `simple_web_html_layout_renderer_core.spl:2987` -> `apply_decls` | ~17,700-22,700 of 25,229 | per-node algorithmic + per-char text parse, no cache. The repo's own comment at `:2965-2969` already says apply_decls is "70-90% of per-node cost" and "unpacks/repacks the ~176-field Style struct"; the accumulated declaration TEXT is re-parsed per node even when byte-identical across nodes sharing a class. |
| 2 | `simple_web_html_layout_renderer_core.spl:2944` `selector_group_matches_node_parts` (def `:2211`) | rest of 25,229 | per-node x per-candidate-rule algorithmic. Already bucketed by `style_rule_candidates` (`:2929`), which is why it is the smaller half. |
| 3 | `simple_web_html_layout_renderer_paint_layout.spl` `resolve_font_metrics_with_language`, from `_simple_web_layout_compose_retained` | 2,959 | redundant work — a SECOND font-metric resolution per `#text` node, distinct from style's (named at `simple_web_html_layout_renderer.spl:1886-1889`). |
| 4 | layout pass, `simple_web_html_layout_renderer.spl:1875` | 651 | per-node algorithmic; proportionate, not a hotspot. |
| 5 | `parse_html`, from `simple_web_html_layout_renderer.spl:1811` | 611 | per-char tokenize; proportionate, not a hotspot. |

Raster (88.8%) is Engine2D backend territory and deliberately not profiled here.
Leaf #1 is filed, not fixed:
`doc/08_tracking/bug/web_style_cascade_apply_decls_reparses_per_node_2026-09-12.md`.

## `sample_web_renderer_sanity.html` runs: measured an EMPTY document

Read these as a caveat, not as evidence. `env_get()` returns `""`, not `nil`, so
`env_get("PROBE_HTML") ?? "<default>"` never took the default: those runs had
`html_bytes=0` and `backend_requested=""`. They still show the pipeline term
(6 ms/frame before, 6 ms on frame 0 and **0 ms with `cache_hit=true` on frames
1-7** after) but say nothing about any backend. **No vulkan-backed run was made
at all, so this profile makes no claim about F10's 18 ms native-readback lane.**
At 1920x1080 — empty document only, no loaded-document 1080p run was made —
frame totals were 62.6-67.4 s before and 61.9-66.1 s after, i.e. unmoved, as
expected on a per-pixel-dominated lane.
