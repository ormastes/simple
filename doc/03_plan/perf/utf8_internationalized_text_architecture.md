<!-- codex-design -->

# UTF-8, Internationalized Text, and Rendering Performance Plan

## Baseline

Capture the pinned snapshot and each implementation wave on matched hardware with monotonic high-resolution timing, setup excluded, deterministic corpus hashes, forced scalar/backend identity, frequency/core conditions, compiler/runtime hashes, Unicode/CLDR/font manifest hashes, and raw SDN/JSON receipts.

## Stage timers

Measure validation/decode, normalization, segmentation, BiDi, itemization, fallback, shaping, line layout, hit testing, raster hit/miss, atlas allocate/evict/upload, batch preparation, vertex/instance construction, submit-to-device completion, fence observation, readback, and presentation independently.

## Memory counters

Record allocations, allocated/copied bytes, retained and transient workspace, builder growth/waste, checkpoint bytes, shaped-run/cache bytes, catalog/table mapped/resident/linked bytes, atlas used/waste/dirty/upload bytes, transient GPU buffer bytes, VRAM high-water, steady and peak RSS, and noalloc high-water/capacity failures.

## Workloads

Use the corpus/profile/backend/size matrix in the system-test plan. Add realistic Simple source, repository documentation, localized catalogs, short UI labels, paragraphs, dense 4,096-glyph HUD, 1/10/100/1000 world labels, atlas churn, mixed-script fallback, RTL/Indic shaping, emoji/color faces, camera motion, depth churn, and device loss/recovery.

## Initial gates

- ASCII compiler wall time: >1% median regression triggers review.
- ASCII lex-only and existing byte/search operations: >2% regression triggers review.
- parser allocated bytes/peak RSS: >2% regression triggers review.
- direct transcoding: no O(scalar-count) intermediate and at most output/bounded-sink storage plus decoder state.
- plain traversal: zero side-index allocation; warm rendering: zero rasterization and zero atlas upload.
- one new glyph: dirty-region upload only after P8; full-atlas upload is an open blocker.
- i18n-disabled/tiny: no unexplained linked/resident locale, catalog, shaping, or renderer capability.
- frame path: no per-draw native-buffer allocation after P9; compatible calls merge in a frame arena/ring.
- all accepted time improvements also pass memory gates; all accepted memory improvements also pass hot-path latency gates.

## Receipt status

The current retained shared-font evidence with `status=unavailable`/`reason=measurement-started` is baseline infrastructure evidence only. It cannot satisfy a performance row. Engine3D currently has RSS-only evidence; HUD/world latency, throughput, scene composition, upload, queue-device, and readback rows remain open.

## First retained portable-host baseline (2026-08-26)

`test/05_perf/text_i18n/utf8_internationalized_text_perf_spec.spl` passed 2/2
on the current x86_64 Linux host through the pure-Simple test child:

- UTF-8 validate + code-point count, 65,536 ASCII bytes: p50 573 us, p95 721 us;
- UTF-8 validate + code-point count, 65,530 multilingual bytes: p50 625 us, p95 666 us;
- UTF-16 to UTF-8, 32,765 input code units: p50 896,299 us, p95 939,137 us;
- peak process RSS after conversion: 62,708 KiB.

These are portable smoke results, not forced-SIMD evidence and not a matched
before/after claim. The UTF-16 result records the existing intermediate-array
cost; remediation is tracked in
`doc/08_tracking/bug/utf16_to_utf8_intermediate_array_perf_2026-08-26.md`.
