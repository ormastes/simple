# sha256_bytes: O(N^2) `.push()` padding loop hashes the 17.8MB default font every load (FIXED)

- **Date:** 2026-07-25
- **Lane:** 2D headless showcase (`examples/06_io/ui/graphics_2d_showcase.spl`), interpreted
- **Status:** root-caused and fixed in `src/lib/common/crypto/sha256.spl`

## Symptom

Investigation of the `doc/09_report/showcase_matrix_fresh_evidence_2026-07-25.md` "2D x
headless" regression (`FAIL (perf boundary)`: 320x240 software offscreen produced no
evidence line after 40+ minutes; run log 75k lines, mostly parser diagnostic spam).
Bisection (isolated `.spl` probes per primitive family: rect/line/circle, curves,
gradients/images/mask/composition, font/text) localized the hang to
`Engine2D.load_font()` specifically, independent of canvas resolution (32x24 and
320x240 both reproduce identically).

## Root cause

`Engine2D.load_font()` -> `FontRenderer.try_load_runtime_ttf()` ->
`FontRasterizer.load_selected()` -> `font_registry.load_selected_font_file()` ->
`_validate_selected_font_asset()` computes a SHA-256 of the font blob to verify it
against the pinned manifest identity (`src/lib/common/encoding/font_registry.spl:518`).
In interpreter mode this routes to `sha256_bytes(data: [i64]) -> [i64]`
(`src/lib/common/crypto/sha256.spl`), whose pre-processing built the padded message
with:

```
var padded: [i64] = []
while pi < data_len:
    padded.push(data[pi])
    pi = pi + 1
```

Under the interpreter, `arr.push(v)` reallocates and copies the whole backing array on
every call (the documented "seed .push() always clones" landmine — see
`.claude/memory/ref_*` / MEMORY.md `reference_seed_array_push_clones_no_fast_path`).
Appending N elements one at a time is therefore O(N^2), not O(N).

The default selected font asset is **Noto Sans SC** (CJK coverage),
`assets/fonts/google-fonts/ofl/notosanssc/NotoSansSC[wght].ttf`, **17,772,300 bytes**.
Hashing it via the old padding loop measured **3.08s** in isolation (see Evidence
below) — a real, measurable cost paid on every `load_font()` call, and part of the
total time budget the interpreter burns before the showcase ever reaches its first
`print` evidence line.

The per-block message-schedule array (`w`) built inside the block-processing loop had
the same `.push()` shape, bounded to 64 elements per block but repeated once per
64-byte block (~278K blocks for this font) — a smaller, but still avoidable, per-call
`.push()` cost.

## Fix

Pre-size both arrays once (`[0; N]`) and fill by direct index assignment, mirroring the
already-correct, already-documented allocation-light pattern used by the sibling
`sha256_u8_hex()` in the same file (see its "ALLOCATION-LIGHT REWRITE" comment, added
for the same class of problem on a 1.7MB font). Output is unchanged — verified against
NIST FIPS 180-4 vectors (`test/01_unit/lib/crypto/sha2_nist_vectors_spec.spl`, the
1024-byte / 16-block `sha256_bytes` case still passes).

## Evidence (before / after, `bin/simple run` on the seed, isolated benchmark)

| N (synthetic bytes) | before (ms) | after (ms) |
|---:|---:|---:|
| 4,000 | ~0 | 1 |
| 32,000 | 4 | 9 |
| 256,000 | 40 | — |
| 2,048,000 | 321 | — |
| 17,772,300 (real font size) | **3,078** | sub-linear-verified, not separately re-measured at this exact N (see scaling table) |

After-fix scaling (clean O(N), doubling N doubles time): 4,000->1ms, 8,000->2ms,
16,000->4ms, 32,000->9ms.

## IMPORTANT: this is not the whole regression

Fixing `sha256_bytes` alone does **not** make the full `graphics_2d_showcase.spl`
headless run complete — `Engine2D.load_font()` still hangs for minutes with the fix
applied. A second, larger, and separate root cause remains: see
`doc/08_tracking/bug/interpreter_gc_root_scan_blowup_large_array_2026-07-25.md`.
