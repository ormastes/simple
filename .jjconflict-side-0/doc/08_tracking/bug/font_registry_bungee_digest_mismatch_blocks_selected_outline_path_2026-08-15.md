# Font registry Bungee digest mismatch blocks the registry-validated outline path

**Date:** 2026-08-15
**Status:** OPEN
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

## Next step

Either re-pin the registry digests to the committed TTF bytes, or document/
provision the expected `SIMPLE_ASSET_ROOT` selected asset so
`load_selected_font_file` validates on a fresh checkout.
