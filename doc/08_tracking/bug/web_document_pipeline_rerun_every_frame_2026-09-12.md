# The web document pipeline re-ran parse+style+layout+Draw IR on every frame (2026-09-12)

Status: FIXED (steady-frame cache landed in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl`).
Platform: macOS 25.5.0 / Apple M4, `SIMPLE_EXECUTION_MODE=interpreter`.
Follows: `vulkan_damage_path_dead_interpreted_copy_2026-09-12.md` (F10) and
`doc/10_metrics/ui/web_render_frame_profile_macos_2026-09-12.md` (F8's profile).

## Symptom

The 09-12 frame profile recorded, in its own words: "Does layout re-run on
steady frames? YES — parse, style, layout and Draw IR build all re-run on every
frame, no cache", and then correctly dismissed it as 0.2% of a 5,000 ms
pixel-dominated frame. F9's native readback and F10's damage path removed the
pixel term. On the native-readback lane the steady frame is ~18 ms at 900x760
and the ~10 ms document pipeline is now the single largest component of it —
the same defect, promoted to dominant by the fixes above.

Nothing in those four stages depends on the frame number. The composed result
for an unchanged document at an unchanged viewport is bit-for-bit the result of
the previous frame, and was being recomputed anyway.

## Fix

A one-entry document cache at `_simple_web_layout_render_html_engine2d_execution`
— the single funnel every web render entry passes through.

- **Key**: viewport w/h, animation clock, retry mode, scroll offset, render
  budget floor, `SIMPLE_WEB_RENDER_BUDGET_MS`, and the html source length; the html source
  itself is then compared **by value**. A per-frame sha256 over multi-KB markup
  in the interpreter would cost more than the pipeline it replaces, so the
  digest facade is deliberately not used on this path; the length is in the key
  so the value compare is reached only for same-length candidates.
  There is deliberately NO device-scale or font-set term: `vector_fonts` is a
  hardcoded `true` at every entry reaching this funnel and no device-scale input
  reaches the compose at all, so keying on `SIMPLE_UI_DEVICE_SCALE` /
  `SIMPLE_VECTOR_FONTS` (tried, then removed) would have been false coverage —
  `/usr/bin/grep -rn` finds no reader for either in `src/lib`.
- **Painting is not cached.** Only parse/style/layout/Draw IR build are skipped;
  the composition is re-executed on the backend every frame, so damage, device
  state and readback behave exactly as before.
- **Bypass, not a wrong answer**, for frames carrying inputs the key does not
  name: any non-empty animation instance list or image resource list skips the
  cache entirely and behaves as before.
- **A degraded render is never cached.** Its composition is a budget-truncated
  document; caching it would republish a truncated frame as a complete one on
  every later frame. Both the result's own `render_degraded` field and the
  module-global latch are checked.
- **The degrade latch is cleared on a hit.** It is normally cleared by STARTING
  a render (`_web_budget_begin`), which a hit skips, so
  `simple_web_layout_clear_render_degraded()` was added to the foundation module
  and is called on every hit. Since only non-degraded results are ever cached,
  this cannot launder an exhausted render into a clean one.
- **`web_document_cache_drain()`** drops the entry for any input the key does not
  name (a font-set reload is the known one — no public font-generation accessor
  is reachable from `browser_engine`, so this is an explicit hook rather than an
  implicit key axis). A drain only ever costs a recompose.

Counters for evidence: `web_document_cache_hit()`, `web_document_cache_hit_count()`,
`web_document_cache_miss_count()`, `web_document_pipeline_ms()`, plus a
`[web-phase] phase=document` receipt under the existing `SIMPLE_WEB_PHASE_TRACE=1`.

## Spec

`test/02_integration/gpu/web_document_pipeline_cache_spec.spl` — every example
pairs the cache counter with an ABSOLUTE pixel oracle, so a key missing an axis
fails on pixels rather than on bookkeeping: the fixture is a right-anchored box
whose painted column is a function of the viewport width.

## Measured (same tree, same binary `39368072 1789171430`, load 3.0)

`examples/06_io/ui/web_catalog/css-layout.html` — 40,960 bytes, **908 DOM
nodes** — at 900x760 on `cpu_simd`:

| frame | total ms | document pipeline ms | cache_hit |
|---|---|---|---|
| 0 (cold) | 263,636 | 29,451 | false |
| 1 | 217,707 | **0** | true |
| 2 | 216,513 | **0** | true |
| 3 | 215,567 | **0** | true |

`hits=3 misses=1`. The whole 29.5 s pipeline disappears on a hit — **17% of the
steady frame** on a real catalog page, entirely from not recomputing an
unchanged document. Frame 0 is unchanged, as required.

A second fixture, `sample_web_renderer_sanity.html`, was also run 8 frames at
900x760 and 1920x1080 with the two lib files reverted to `origin/main` in the
SAME worktree (before) and in place (after): pipeline 6 ms on every frame
before, 6 ms on frame 0 and 0 ms with `cache_hit=true` on frames 1-7 after.
**Those runs measured an EMPTY document** — `env_get()` returns `""` not `nil`,
so the probe's `?? "<default>"` never took the default (`html_bytes=0`) and the
backend name was `""` too. They are retained as a caveat, not as evidence, and
they make no claim about any backend lane. Full numbers:
`doc/10_metrics/ui/web_catalog_cold_render_profile_macos_2026-09-12.md`.

## Sabotage

Deleting the width term from `_web_document_cache_key` turns the viewport
example red on its pixel oracle (the wide render republishes the narrow
render's right-anchored box), restoring it turns it green. Measured with the seed
(`src/compiler_rust/target/bootstrap/simple run`): **5 examples, 0 failures** ->
sabotage **5 examples, 1 failure** (`a viewport change is a miss, and moves the
right-anchored box`) -> restore **5 examples, 0 failures**.
