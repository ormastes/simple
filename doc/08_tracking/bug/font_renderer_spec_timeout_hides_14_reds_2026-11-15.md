# font_renderer_spec: a 900 s timeout hid 15 failing rows

Status: RESOLVED 2026-11-15 on `work/font-spec-green-20261115` (all 14 rows; see "Resolution"). Triaged on `work/engine2d-parity-4-20261115`. The
slow row and a stale lock contract are fixed; 14 real reds remain.

## What the timeout hid

`test/01_unit/lib/common/text_layout/font_renderer_spec.spl` (49 rows) never
finished: the worker was killed at the 900 s budget, so the verdict said
`timeout=1` and nobody saw the rows. I split the file into chunks with the same
header and helpers and ran each chunk on its own. Seed 59635056 B, mtime
1794616340, load ~4.

| chunk | rows | wall | result |
|---|---|---|---|
| liveness rows (without registration) | 4 | 85 s | 3 pass, 1 fail |
| registration row alone | 1 | > 800 s | killed (the 902 s chunk minus 85 s) |
| program version + dependency generation | 8 | 6 s | 7 pass, 1 fail (fixed below, now 8/8) |
| shared font renderer fallbacks, part 1 | 18 | 13 s | 8 pass, 10 fail (2 were missing-helper artefacts of the chunking; 8 real) |
| shared font renderer fallbacks, part 2 | 18 | 239 s | 13 pass, 5 fail |

Base check, scoped to what was actually run:
- The 8 reds of "fallbacks, part 1" fail identically at `766838d20de`, the tree
  before the atlas size-retention change (#9491). That includes both
  atlas-reset rows, so they are not regressions from that PR.
- "Fallbacks, part 2" (5 reds) and the sha-pin row were NOT re-run at the base.
  Their origin is unverified.

## Fixed here

- **Slow row.** "registers exact bytes for every selected identity and
  rejects corruption" hashes all 16 pinned faces (~52 MB) twice: once with
  the same-length corrupted blob and once with the good one. In the spec
  child that costs more than 800 s; under `simple run` registering one 17.7 MB
  face takes 0.64 s. The row moved, assertions unchanged, to
  `font_renderer_selected_registration_spec.spl`, where it is still honestly
  slow. Measured alone at the PR head: `timeout=1 reason=daemon-worker-timeout
  budget_ms=899981` (901 s wall, 0/1). The split isolates the red; it does not
  fix it. Open: make the spec lane hash at `run` speed, or validate the size and
  header before the full digest. Do not raise the budget.
- **Stale copy.** "uses facade-owned locks with a freestanding-safe lazy path"
  pinned `mutex_lock`, but `26e2ca12c9f` renamed the callers to
  `mutex_lock_gate`. The contract text is updated.

## Open reds (owner per row; base status as scoped above)

| row | observed | first read |
|---|---|---|
| renders a selected face from owned bytes without a hosted dylib | sha `00a67785...` vs pinned `65f5480a...`; quad still 18x23, glyph shape correct, 182 ink px | rasterizer output drifted since the 2026-09 pin; not bisected |
| ignores forged vector glyph environment | 11 vs 3, 24 vs 2 | forged-env guard or the counted fixture changed |
| maps multibyte Draw IR advances by UTF-8 byte offset | 2 vs 3 | byte-offset mapping (see text slice = bytes owner decision) |
| resets and repacks the atlas when the face generation changes | dirty 0 vs 1 | cause not localised; already red at `766838d20de` |
| resets and repacks the atlas when identity changes at the same generation | dirty 0 vs 1 | same as above |
| renders bitmap glyph fallback with exact mask evidence | 7 vs 8 | bitmap mask count |
| keeps provided browser sans and mono candidates ahead of host fallbacks | Liberation/DejaVu ahead of the bundled Noto | Chrome-159 candidate order (`01fc2aed388`, `6e1c57e47d6`); oracle likely stale, needs the web-lane owner |
| maps browser CSS font-family names to provided font lanes | DejaVuSansMono vs NotoSansMono | same |
| puts resolved local font-face sources ahead of generic fallback candidates | NotoSerifSC vs NotoSerif-Regular | same |
| exposes an opt-in browser default font materialization surface | path list differs | same family |
| resolves accepted Arabic through a handle-free shaped cluster payload | `SffiGlyphBitmap` has no `bearing_x` | API drift in the spec |
| shaped-run cache: STRESS | hits 0 vs 1 (each key) | shaped-run cache records no hits |
| shaped-run cache: repeated identical shaping records a hit | hits 0 | same |
| shapes registered-only Arabic and Devanagari without filesystem reads | `font-shaping-unavailable` vs `resolved` | registered-bytes shaping path |

Confirmed by one complete run of the trimmed spec (same seed, load ~4):
`48 total, 34 passed, 14 failed`, in 333 s, under the 900 s budget. The 14
failing names are exactly the rows above. The split-out registration spec is
still too slow for the budget and is tracked by the open item under "Fixed here".

## Sibling: shared_font_surfaces_spec (4/6, then 6/6)

`test/03_system/app/simple_2d/feature/shared_font_surfaces_spec.spl` held two
stale copies of an API that has since moved:
- `config.identity()` is now the free function `font_render_config_identity(config)`.
- `cache_identity_snapshot()` was split into `cache_identity_generation()` and
  `cache_identity()` (`53b99dbed07`).

Updated with the same assertions; 6/6.

## Resolution (2026-11-15, `work/font-spec-green-20261115`)

The 6 unverified rows were re-run on the pre-#9491 tree `766838d20de`, and
all 6 fail there too. #9491 introduced none of the 14 rows.

Each row got its introducing commit. Rows marked "stale" had an oracle the
product had deliberately moved past. Rows marked "defect" were product bugs,
fixed TDD (red row first).

| row | class | introducing commit | change |
|---|---|---|---|
| renders a selected face from owned bytes | stale pin | a03073da786 (07-20, 4x4 supersampled coverage; it re-pinned sfnt_glyf_spec only) | re-pinned to `00a67785...`. Proof: restoring only the old `_glyf_edge_coverage` reproduces the old pin `65f5480a...` exactly |
| ignores forged vector glyph environment | stale body | c318743c34b (07-15) set the "ignore" contract; by 88aac2ffe28 (09-29 transplant) the body had reverted to the old accept-payload assertions | restored the c318743c34b body (batch equals the batch without the forged env) |
| maps multibyte Draw IR advances by UTF-8 byte offset | defect | fallback LayoutGlyph producers counted codepoints, and the requad mirror used the loop index | the producers in `font_renderer.spl` now emit UTF-8 byte offsets (owner decision 2026-11-13). `font_batch_apply_advances` already accepted either index space |
| resets and repacks the atlas (generation; identity) | stale oracle | atlas park/restore (present by bb3f6ab8ab2): a switch restores the incoming owner's park | the rows mark the whole atlas, including `atlas_active_park_key`, as another owner's. Asserts reset + 1 dirty rect + exactly one park under the stale key |
| renders bitmap glyph fallback with exact mask | defect (order-dependent) | T12 cross-instance raster cache (2026-08-07) keyed `"";cp;fs` for every renderer without a rasterizer | the key now carries the fallback tier (`fallback=vector/bitmap/ttf/none`). New row: "keeps vector and bitmap fallback tiers apart" (red 7 vs 8, then green). The bisect showed the identity-reset row leaking the vector 'A' into the bitmap row |
| sans/mono candidates, CSS family lanes, local font-face, materialization | stale oracle | 571e316f856 (07-11, bundled faces moved to the registry assets) plus the Chrome 159 per-name resolver | exact Linux pins on the measured host (Liberation Sans, DejaVu Sans Mono), composition pins elsewhere |
| Arabic handle-free shaped cluster | stale copy | `gbm_*` field rename; bbb98e957a8 (07-27) took the selected-face ascent from the outline | `gbm_*` fields; ascent from `sfnt_measure_glyph_into` meta[17], pinned to 44 |
| shaped-run cache STRESS; repeated hit | stale oracle | resolved-metric front memo (present by bb3f6ab8ab2) answers repeats before the deep cache | asserts front-memo hits, and adds a case-folded variant (`Sans-Serif`) that must be a deep-cache hit |
| shapes registered-only Arabic and Devanagari | defect | f119f8b7120 (07-28, canonical OT layout) gated layout on a live host handle and dropped the handle-free acceptance from 83e55dfe6d7 | `shaper_with_registered_ot_font(shaper, font, pinned_hex)`, accepted only for a handle-free run font whose registry identity carries that digest. New negatives in `test/01_unit/lib/skia/shaper_spec.spl`: plain binding, wrong digest, unpinned path |

Only the hosted registered-only lane was exercised. There was no SimpleOS or
baremetal run.

Full-file verification, 2026-11-15, seed `cargo-target-webrender-vk/release/simple`,
load average 10.25: `Results: 49 total, 49 passed, 0 failed`. Wall time was
342 s against a 900 s budget. Outer maxrss was 245,356 KB.
