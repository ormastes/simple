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

## Direct-raster isolation (2026-09-04)

A focused follow-up temporarily removed `FontRasterizer` and called the same
pure-Simple `sfnt_measure_glyph_into` / `sfnt_render_glyph_into` owners directly.
This confirmed that the benchmark can separate raster cost from asset loading,
but the Phase 2 compiler cannot admit the resulting narrow closure:

- the compatibility SFFI import poisons HIR with unresolved
  `file_read_bytes` and `thread_sleep`;
- importing `std.nogc_sync_mut.io_runtime` directly expands into an oversized
  closure, emits unresolved-method const-zero placeholders, and remained in
  MIR lowering at 100% CPU with no new log progress for seven minutes;
- importing `std.nogc_sync_mut.io.file_ops` directly still poisons HIR with
  unresolved `file_read_bytes`, `getpid`, `read_file_text`, `process_run`, and
  `rename_path`.

All three attempts used `SIMPLE_NO_STUB_FALLBACK=1`; no output was admitted and
the experimental producer edit was reverted. The next compiler fix must make a
narrow owner import reachable without wildcard-facade loss or unrelated I/O
closure expansion. Do not bypass this with a copied executable or weak stubs.
