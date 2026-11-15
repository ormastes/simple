# font_renderer_spec: a 900 s timeout hid 15 failing rows

Status: OPEN, triaged 2026-11-15 on `work/engine2d-parity-4-20261115`. The
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

Every red in the last two chunks also fails at `766838d20de`, the tree
before the atlas size-retention change (#9491). They are not regressions from
that PR.

## Fixed here

- **Slow row.** "registers exact bytes for every selected identity and
  rejects corruption" hashes all 16 pinned faces (~52 MB) twice: once with
  the same-length corrupted blob and once with the good one. In the spec
  child that costs more than 800 s; under `simple run` registering one 17.7 MB
  face takes 0.64 s. The row moved, assertions unchanged, to
  `font_renderer_selected_registration_spec.spl`, where it is still honestly
  slow. Open: make the spec lane hash at `run` speed, or validate the size and
  header before the full digest. Do not raise the budget.
- **Stale copy.** "uses facade-owned locks with a freestanding-safe lazy path"
  pinned `mutex_lock`, but `26e2ca12c9f` renamed the callers to
  `mutex_lock_gate`. The contract text is updated.

## Open reds (pre-existing, file and owner per row)

| row | observed | first read |
|---|---|---|
| renders a selected face from owned bytes without a hosted dylib | sha `00a67785...` vs pinned `65f5480a...`; quad still 18x23, glyph shape correct, 182 ink px | rasterizer output drifted since the 2026-09 pin; not bisected |
| ignores forged vector glyph environment | 11 vs 3, 24 vs 2 | forged-env guard or the counted fixture changed |
| maps multibyte Draw IR advances by UTF-8 byte offset | 2 vs 3 | byte-offset mapping (see text slice = bytes owner decision) |
| resets and repacks the atlas when the face generation changes | dirty 0 vs 1 | the poked `atlas_face_generation` is answered by the park/restore path, not a reset |
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
