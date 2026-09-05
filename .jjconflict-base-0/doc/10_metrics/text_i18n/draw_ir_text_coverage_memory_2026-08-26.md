# Canonical Draw IR text coverage and memory — 2026-08-26

The direct `draw_ir.spl` suite passes 17/17 with 100% branches (33/33) and 86%
lines (123/143). It covers Unicode shaped payloads, every malformed payload and
resolved-metric class, clips/intersections, nested composition prefixing,
handle-free embedding, every event target class, unresolved/stale scenes, and
CPU/GPU/auto/metal selection and fallback for batches and compositions.

The semantic construction smoke passes 1/1. Seven samples each created 256
four-glyph multilingual shaped commands and a composition plan: p50/p95
42,534/166,907 us, process HWM 53,028 KiB, checksum 1,820. The run was
interpreter-demoted and allocation/retained bytes are unavailable.

Atlas and device bytes and draw calls are structurally zero because this owner
contains only semantic, handle-free IR. This result does not qualify shaping,
`FontRenderer`, Engine2D execution, GPU submission, or device readback.
