# Font registry Bungee digest mismatch blocks the registry-validated outline path
## Historical registration heading: Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-08-15
**Status:** CLOSED — the reported digest-mismatch premise compared the TTF pin with the distinct `METADATA.pb` pin.
**Found while:** building the Chrome vector-font differential lane
(`tools/vector_font_diff/`, `test/03_system/browser_engine/chrome_vector_font_differential_spec.spl`).

## Symptom

Every registry-validated outline load of the repo's canonical vector font fails
soft on this checkout:

- `font_sffi.load_font("assets/fonts/google-fonts/ofl/bungee/Bungee-Regular.ttf")` → `nil`
- `FontRasterizer.load_selected(...)` and `FontRasterizer.load(dylib, bungee_ttf)` →
  `loaded_generation == 0` (invalid)

All fail in `load_selected_font_file` validation, not in the rasterizer.

## Evidence

- `sha256sum assets/fonts/google-fonts/ofl/bungee/Bungee-Regular.ttf` =
  `c4f5361ce120af3e6b9156d0bf379fa19cda2ea0cd18ac01fd99596c6bf66e3f`
- Pinned digest in `src/lib/common/encoding/font_registry.spl`
  (`_font_candidate_*_sha256`, family "Bungee") =
  `ec1a73318ff76d666c2e3cad5948b6799f4a9ed6d6af59e787f4e5372c291edf`
- `selected_font_asset_candidate_for_path(bungee_path)` is non-nil, so the
  registry-managed branch is taken and the mismatched digest rejects the blob.
- The rasterizer itself is fine: initializing the spl_fonts cdylib directly with
  a NON-registry TTF (`rt_fonts_init` on DejaVuSans) rasterizes correctly and
  matches Chrome ink metrics within tolerance (see
  `tools/vector_font_diff/out/summary.txt`).

## Impact

Production text rendering silently falls back to the bitmap-font path whenever
the Bungee outline is requested through the registry on a checkout whose TTF
bytes differ from the pin (the registry may expect a subsetted/installed
"selected" asset under `SIMPLE_ASSET_ROOT`; unset here). The vector-font
differential lane works around it by using a non-registry TTF (DejaVuSans), so
the outline rasterizer is still gated — but the registry-validated Bungee lane
is not.

## Historical next step (superseded by the closure adjudication below)

Either re-pin the registry digests to the committed TTF bytes, or document/
provision the expected `SIMPLE_ASSET_ROOT` selected asset so
`load_selected_font_file` validates on a fresh checkout.

## Closure adjudication — 2026-10-27

The original digest-mismatch premise is invalid. The Bungee TTF bytes at
`assets/fonts/google-fonts/ofl/bungee/Bungee-Regular.ttf` hash to
`c4f5361ce120af3e6b9156d0bf379fa19cda2ea0cd18ac01fd99596c6bf66e3f`.
The different value `ec1a73318ff76d666c2e3cad5948b6799f4a9ed6d6af59e787f4e5372c291edf`
is the hash of `assets/fonts/google-fonts/ofl/bungee/METADATA.pb`. In
`src/lib/common/encoding/font_registry.spl`, `_font_candidate_metadata_sha256`
returns that metadata pin; the Bungee `_google_font_candidate` row supplies the
TTF pin as its separate `sha256` argument, and validation compares the actual
font digest with `candidate.sha256`. The committed bytes match both distinct
pins. V4 review evidence also checked these source blobs at assessed commit
`c0b3ad911f4cb00c0f3550b05baa8d06347d17d0` and pre-report source commit
`ae55a7467197350bdf8b91c48444c167219ce8bb`.

This closes only the false digest-mismatch diagnosis. It does not explain the
historical nil-loading or fallback symptoms and does not claim that Bungee
loading, rasterization, or a runtime path passed. Those symptoms remain
unqualified. The canonical ledger keeps `valid=true` so the record remains
visible; it is closed because this report's stated premise was invalid. The
original report date and historical evidence above are retained.

