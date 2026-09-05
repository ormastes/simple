<!-- codex-design -->

# UTF-8, Internationalized Text, and Rendering System Test Plan

## Evidence classes

- `reference`: scalar oracle and official conformance vectors;
- `portable`: optimized Simple implementation compared to reference;
- `forced-backend`: named compiled SIMD/GPU implementation with active-backend attestation;
- `source-contract`: ownership/static invariants only;
- `native-device`: submission through device completion and device-origin readback;
- `blocked`: required row lacks its native host/tool/artifact and remains open.

## Frozen primary flow

The canonical acceptance spec shall display these steps exactly and in order:

1. `Load the pinned multilingual font manifest`
2. `Accept exact-face-bound simple-script shaping`
3. `Prepare one shared font batch for 2D and 3D`
4. `Emit the selected font composite program and plan compilation`
5. `Prove native submission and device readback`

Existing specs are supporting evidence. The current occurrence of step 3 compares Engine2D CPU/SIMD and does not prove shared Engine2D/Engine3D consumption; the replacement checker must assert identical renderer owner, face/config/generation, atlas identity, quad data, and immutable batch content across both consumers.

## Requirement traceability

| Requirements | Scenarios |
|---|---|
| REQ-001..004 | safe construction; boundary slicing; scalar movement; strict/lossy decode; every short chunk/output partition; unknown labels; fixed capacity |
| REQ-005 | old/new lexer differential; ASCII block scan; multilingual identifiers; string/f/i18n scanner; byte/UTF-16/LSP spans |
| REQ-006 | official normalization, grapheme, word, sentence, BiDi, line-break, XID, case, and security vectors |
| REQ-007..008 | stable IDs; schema mismatch; plural/select; fallback; isolation; one-pass sink; concurrent locale contexts; dead-strip/noalloc |
| REQ-009..010 | Draw IR semantic and shaped SDN round-trip; malformed payload rejection; GUI/Web/WM production route; Engine2D batch/readback |
| REQ-011..013 | shared batch; HUD, screen label, spherical/cylindrical billboard, fixed plane, depth annotation; transform/LOD/depth/color/raster policies |
| REQ-014 | scalar/portable/SIMD/GPU differential, forced dispatch, fuzz and backend inventory |
| REQ-015..016 | compatibility lints/fixes, ABI tests, AST-only extractor parity and line-scanner removal |

## Branch-coverage gate

The compiler's canonical flat-AST inventory and test-runner pre-registration already keep unvisited Simple decisions in the denominator. Coverage acceptance shall reuse that mechanism, add a source/config-hash-bound text/i18n/rendering owner manifest, and report every branch as hit, missed, or reviewed-unreachable. Rust/C owners use `cargo llvm-cov` or the matching compiler-native tool and merge only after file/profile identity is recorded. Forced SIMD/GPU rows must attest actual backend execution.

Coverage owners include changed text/string/codec/I/O/parser/i18n/Draw IR/font renderer/Engine2D/Engine3D modules and adapters. Each error, fallback, capacity, overflow, stale generation, invalid payload, cache miss/eviction, upload, submission, completion, readback, and device-loss branch is injected or exercised. Vendor files remain excluded unless changed.

## Correctness matrices

- encodings: UTF-8/16LE/16BE/32LE/32BE, ASCII, Latin-1, Windows-1252, and selected Shift_JIS/EUC-KR/Big5/GB18030 profiles;
- corpora: ASCII, precomposed/decomposed Latin, Hangul/Jamo, CJK, Arabic/Hebrew/BiDi, Indic, Thai, emoji/VS/modifier/ZWJ, long combining sequences, malformed structural classes;
- sizes: 0..8, 15/16, 23, 31/32, 63/64, 127/128, 255/256, 1 KiB, 4 KiB, 64 KiB, 1 MiB, 64 MiB;
- profiles: GC/no-GC × sync/async × mutable/immutable, noalloc/tiny, default-only/single/multi-locale;
- CPU: scalar, SSE2, AVX2, AVX-512, NEON/SVE, RVV, wasm where compiled;
- render: CPU oracle, Vulkan, CUDA, Metal, DirectX and other selected adapters, with unavailable native rows blocked.

## Rendering scenarios

- identical immutable batch through Engine2D, Engine3D HUD, and Engine3D world;
- 1/10/100/1000 calls, repeated/new glyphs, one/three faces, empty/clipped/offscreen;
- warm cache causes zero rasterization and upload; one new glyph dirties/uploads only its rectangle;
- scene geometry before/after translucent/opaque world text, near/far order, coverage-aware depth, HUD depth ignore;
- spherical/cylindrical/fixed placement across camera roll/yaw/pitch, perspective, near/far/frustum, anchor/pivot, multiline/RTL/vertical/emoji clusters;
- unsupported CTM/LCD/color/target and Required/Preferred/Suggested policies reject/fallback exactly before mutation;
- atlas eviction, resize, upload failure, completion unknown, device loss, reinstall, and stale batch generation;
- semantic accessibility, reading order, selection/caret/hit-test geometry remains stable across pixels and visual reorder.

## Performance gates

The matching perf spec belongs under `test/05_perf/text_i18n/` with a mirror under `doc/06_spec/05_perf/text_i18n/`. It records cold/warm p50/p95, throughput, cycles/byte where available, allocations/bytes/copied/transient workspace/RSS/binary/data size, cache/atlas/VRAM, uploads/draws/buffers, CPU/GPU stage times, fallback, backend, corpus, config, manifest, and commit/toolchain/hardware identity.

Readback is measured separately from normal frame time. `queue_device` is submit through device completion and is not added to later fence observation. Baselines are matched-machine only. Unavailable or `measurement-started` receipts are not PASS.

## Planned executable artifacts

- `test/03_system/app/text_i18n/feature/utf8_internationalized_text_architecture_spec.spl` — present; source-contract evidence passes 3/3.
- `doc/06_spec/03_system/app/text_i18n/feature/utf8_internationalized_text_architecture_spec.md` — present; 101 documentation lines, zero stubs/warnings.
- `test/05_perf/text_i18n/utf8_internationalized_text_perf_spec.spl` — present; portable-host baseline passes 2/2.
- `doc/06_spec/05_perf/text_i18n/utf8_internationalized_text_perf_spec.md` — present; 115 documentation lines, zero stubs/warnings.
- focused unit/integration specs beside each owner rather than one giant source-inspection spec.

Scaffolds remain fail-closed until production entrypoints exist. Generated manuals must report zero stubs before acceptance and be readable without opening executable source.

The required `sspec-maintain scan` is currently blocked by the deployed
compiler failing to parse `src/lib/nogc_sync_mut/tooling/easy_fix/accessor_rewrite.spl`;
see `doc/08_tracking/bug/seed_redeploy_breaks_test_runner_accessor_rewrite_parse_2026-08-25.md`.
