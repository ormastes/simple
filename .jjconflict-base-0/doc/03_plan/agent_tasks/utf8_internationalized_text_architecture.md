<!-- codex-design -->

# UTF-8, Internationalized Text, and Rendering Agent Plan

## Shared contract

All lanes use the interfaces and five manual steps frozen in `.spipe/utf8_internationalized_text_architecture/state.md`. Sidecars cannot rename them, create a competing text/font/rendering owner, or mark broad evidence complete. Merge owner and final reviewer are the root Codex lane.

## Ordered work packages

| Lane | Scope | Depends on | Exit evidence |
|---|---|---|---|
| P0 measurement | repair static branch denominator; deterministic corpora; time/memory/backend receipt schema; pinned baseline | none | baseline and coverage manifest prove missed branches remain visible |
| P1 invariant | constructors, byte/text split, boundaries, scalar oracle, typed errors | P0 | malformed/boundary unit matrix at 100% owned branch coverage |
| P2 views/builders | slices, cursors, sparse index, growable/fixed sinks | P1 | no malformed partial output; allocation/index memory gates |
| P3 codecs/I/O | direct streaming UTF/Latin/legacy codecs; sync/async readers/writers | P1/P2 | every short partition/capacity cut; oracle parity; no scalar array |
| P4 parser | byte/block lexer, borrowed tokens, unified string scanner, source maps, XID/NFC | P0/P1/P2 | token/AST/span differential; ASCII perf/RSS gate |
| P5 Unicode | pinned generator; normalization/segmentation/BiDi/line/XID/security | P1/P2 | official conformance and reproducible table hashes |
| P6 i18n | AST extractor, stable schema/IR/catalog, explicit locale, plural/select/noalloc | P2/P5 | schema/catalog/message branch and perf gates |
| P7 semantic layout | paragraph itemization, fallback, shaping, line layout, clusters, accessibility | P2/P5 | HarfBuzz/reference witnesses and logical/visual mapping tests |
| P8 Draw IR/Engine2D | versioned shaped payload, production GUI/Web/WM route, shared material, dirty atlas | P7 | semantic → batch → native readback ladder |
| P9 Engine3D | HUD/screen/billboard/world/depth modes, scene composition, frame arena/ring | P7/P8 shared material | real scene depth/occlusion, CPU/device parity, 3D perf rows |
| P10 SIMD/GPU | complete forced kernels, centralized dispatch, selected font composite artifacts | P0/P1/P3/P8/P9 | active-backend parity, coverage, perf, device receipts |
| P11 migration/docs | lints/fixes, compatibility removal, guides/wiki/bug/Todo closure | all | traceability, manuals, zero layout violations, final review |

## Parallel ownership

- Lower-model sidecars may audit or implement bounded P3 codec, P5 table, P6 catalog, P8 backend, P9 adapter, and P10 architecture rows after the best-model owner freezes field schemas and fixtures.
- High-conflict files (`string_core.spl`, `utf8.spl`, lexer owner, `font_renderer.spl`, Engine2D/Engine3D engines, runtime dispatch) use serial ownership windows.
- Parent-authoritative integration accepts isolated changes only after focused evidence and reviews generated manuals and done marks.
- External GPU/OS/ISA rows retain owner, host prerequisites, command, artifacts, and final reviewer; unavailable is blocked, never removed.

## Required handoff packet

Each lane reports changed files, semantics, branch-manifest delta, tests/commands run once, baseline/result receipts, allocations/RSS/binary effects, unsupported rows, tracked bugs, conflicts, guide/wiki updates, and exact next dependency. Three distinct failed fix/verify cycles end with escalation rather than another retry.
