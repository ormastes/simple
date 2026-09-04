# Phase 2 native selected-font byte loading returns invalid

## Status

Open after three focused vector-producer cycles; do not retry the identical
build/run in this lane.

## Evidence

The admitted macOS arm64 Phase 2 compiler builds
`vector_font_raster_feature_producer.spl` with
`SIMPLE_NO_STUB_FALLBACK=1`. The resulting Mach-O reads the checked-in
1,708,408-byte Noto Sans Mono asset, then
`FontRasterizer.load_selected_bytes(FONT_PATH, font_bytes)` returns the invalid
sentinel (`loaded_generation <= 0`). The producer emits:

```text
vector_font_simple_status=failed reason=selected-font-load
```

Using `load_selected(FONT_PATH)` failed identically, so bypassing file-backed
loading did not change the result. No fabricated, weak, or unresolved symbol
appears in the strict build transcript.

## Required fix

Trace the native Phase 2 path through selected asset identity validation,
`validate_selected_font_asset`, `font_runtime_ttf_default_supported`, and the
plain `FontRasterizer` aggregate return. Preserve fail-closed manifest/hash
validation. Admission requires the current producer to emit a complete
94-glyph receipt and pass the Chrome accuracy plus C p95 gate.
