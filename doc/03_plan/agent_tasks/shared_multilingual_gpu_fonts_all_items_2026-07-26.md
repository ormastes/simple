<!-- codex-design -->
# Shared Multilingual GPU Fonts — All Remaining Items

## Goal and authority

Requirements remain `doc/02_requirements/{feature,nfr}/shared_multilingual_gpu_fonts.md`.
State and acceptance criteria live in
`.spipe/shared_multilingual_gpu_fonts_all_items/state.md`. This plan supersedes
the scheduling sections—not the historical evidence—of
`shared_multilingual_gpu_fonts.md`.

## Frozen coordination contract

Use only the interfaces, manual steps, and checker names frozen in the state
file. A lane encountering a missing helper must fail explicitly and return the
gap to the merge owner. No lane creates a parallel renderer, shaper, emitter,
atlas, cache, process/env facade, or device-success path.

## Current evidence baseline

| Area | Current evidence | Required next state |
|---|---|---|
| GSUB/GPOS | reviewed completion is integrated on the isolated branch; superseded stage1 duplicates were not imported | execute the frozen shaping/parser specs on the deployed pure-Simple runtime |
| Runtime | compiler/bootstrap deltas and nine compiler-only specs are excluded under `f1bcd0db5be`; the latest isolated lane retained 1,417 objects and parsed all 1,190 files, but cycles 2/3 trapped after the Stage3 final HIR diagnostic `eprint`, so no admitted current full CLI exists | a fresh external P0 resumes `/tmp/simple-cli-admission-20260727-4`, explicitly unsets `SIMPLE_COMPILER_PHASE_PROFILE`, `SIMPLE_COMPILER_TRACE`, and `SIMPLE_BOOTSTRAP_DIAG`, runs one bounded full-CLI cycle, then A records and calibrates its immutable identity |
| Focused tests | implementation and static coverage exist; prior runner exited before examples | calibrated, nonzero, authoritative runtime results |
| Native GPU | source/emission and partial backend evidence exist | one real 2D+3D promoted device route and current perf record |
| Surfaces | source contracts and retained artifacts exist | live canonical Web/GUI/WM/SimpleOS evidence and honest blocked rows |
| Docs/manuals | 32 changed/new sources since `origin/main`; 13 mirrors missing, 19 stale, zero current, and zero retained docgen logs | regenerate all 32 mirrors with the admitted pure-Simple runtime, require `0 stubs`, and update one requirement/evidence matrix |

## Parallel lanes

| Lane | Owner | Exclusive writable scope | Deliverable and evidence |
|---|---|---|---|
| A bootstrap/runner | `bootstrap_runner` | bootstrap/compiler/runtime owner files required by the reproduced admission crash; `build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/**`; bootstrap bug/TODO docs | admitted Stage 4 CLI path+SHA, essential-tools smoke, deliberate-red/empty calibration, exact blocker after max 3 cycles |
| B manifests/distribution | `manifest_distribution` | font registry/assets/notices; release/package/SimpleOS font-manifest specs and mirrored manuals | REQ-001–005, NFR-001/003 executable byte/license/package evidence |
| C shaping/material/config | `shaping_material` | `src/lib/skia/feature/{glyph,shaper}/**`, canonical text-layout/font-renderer files, their unit specs | integrate GSUB/GPOS, exact selected-script shaping, shared batch/cache/config-policy evidence |
| D production surfaces | `surface_simpleos` | Web/GUI/WM/SimpleOS producer adapters and their dedicated system specs/manuals; no renderer internals | canonical Draw IR identity plus hosted and QEMU pixel/input evidence |
| E native 2D/3D/perf | `native_gpu_perf` | existing Engine2D/Engine3D native adapters, font native-readback/perf specs, retained native evidence | REQ-012/013 and NFR-002/004–008 real device proof or exact blocked-host contracts |
| F specs/docs/audit | `spec_docs_audit` | aggregate test plan, guides, state/traceability reports; no product code or owner-specific manuals | map every REQ/NFR, audit all 32 changed/new source-to-manual pairs and owner logs, and reject stale, missing, stubbed, or premature PASS evidence |
| H merge/final verify | `/root` | integration conflict resolution, final evidence report, branch history | primary review, direct-runtime guards, scoped verification once, status, rebase/file-count guard, push |

| Task | Owner | Exclusive writable scope | Dependency | Deliverable and evidence |
|---|---|---|---|---|
| P0 fresh pure-CLI admission | external compiler/runtime owner | separate clean compiler worktree, incremental cache, admission logs; no font-branch files | none | current pure-Simple full CLI plus CLI/core-C paths and SHA-256 identities; essential-tools smoke PASS |
| A1 runtime identity | `bootstrap_runner` | retained runtime identity and focused runner artifacts only | P0 | immutable admitted CLI/core-C identity; reject Rust seed and stale binaries |
| A2 command calibration | `bootstrap_runner` | `build/test-artifacts/shared_multilingual_gpu_fonts/runtime-calibration/**` | A1 | essential-tools, direct lint, direct duplicate-check, deliberate-red, and zero-example evidence |
| B1 manifests/distribution | `manifest_distribution` | font registry/assets/notices, release/package/SimpleOS font-manifest code and specs | A2 | REQ-001–005 and NFR-001/003 executable byte/license/package evidence |
| B2 distribution manuals | `manifest_distribution` | only B-owned mirrored manuals and docgen logs | B1 | current `0 stubs` manuals for B's six changed specs |
| C1 shaping/material/config | `shaping_material` | `src/lib/skia/feature/{glyph,shaper}/**`, canonical text-layout/font-renderer files, their unit/aggregate specs | A2 | reviewed GSUB/GPOS, exact selected-script shaping, shared batch/cache/config-policy evidence |
| C2 shaping manuals | `shaping_material` | only C-owned mirrored manuals and docgen logs | C1 | current `0 stubs` manuals for C's ten changed specs |
| D1 Engine2D capability | `surface_simpleos` | Engine2D production-route spec/manual only; no renderer internals | C1 | `engine2d_font_surface_verification_spec.spl` proves Draw IR text reaches the shared `FontRenderer` path |
| D2 Web capability | `surface_simpleos` | Web producer adapters and Web specs/manuals | D1 | canonical HTML/WebIR → Draw IR identity and visible result |
| D3 GUI capability | `surface_simpleos` | GUI producer adapters and GUI specs/manuals | D1 | widget scene → Draw IR identity and correlated input |
| D4 hosted-WM capability | `surface_simpleos` | hosted-WM producer adapter and dedicated spec/manual/evidence | D1 plus hosted display | canonical hosted frame, glyph crop, and correlated WM input |
| D5 x86 SimpleOS capability | `surface_simpleos` | x86 SimpleOS producer/spec/manual/QEMU evidence | D1 plus x86 QEMU | pinned guest bytes, framebuffer glyph pixels, and correlated QMP input |
| D6 RV64 SimpleOS capability | `surface_simpleos` | RV64 producer/spec/manual/QEMU evidence | D1 plus RV64 QEMU | pinned guest bytes, framebuffer glyph pixels, and VirtIO input |
| D7 surface manuals | `surface_simpleos` | only D-owned mirrored manuals and docgen logs | D2–D6 | current `0 stubs` manuals for D's nine changed specs; unavailable hosts remain blocked |
| E1 deterministic emission | `native_gpu_perf` | existing portable emitter/native adapter specs and retained compile artifacts | A2+C1 | versioned deterministic emission/compile evidence; no execution claim |
| E2 native 2D/3D | `native_gpu_perf` | existing Engine2D/Engine3D native adapters, native-readback spec, retained device evidence | D1+E1 plus real device | texture/upload/bind/draw/fence/device-origin readback for 2D and 3D |
| E3 native performance/manuals | `native_gpu_perf` | native-readback and performance specs/manuals plus retained device/perf evidence | E2 | current `0 stubs` manuals for E's two changed specs; NFR-002/004–008 fixture, p95, hit, CPU/GPU, RSS/VRAM, upload, device/driver record |
| F1 evidence/manual audit | `spec_docs_audit` | aggregate plan, guide, state/traceability reports; no product code or owner manuals | B2+C2+D7+E3 | audit all 32 source/manual/log triples; reject missing, stale, stubbed, simulated, or premature PASS evidence |
| H1 final review | `/root` | integration conflict resolution and final evidence report | F1 | independently map REQ-001–015/NFR-001–008 and run final guards once |
| H2 sync/push | `/root` | branch history only | H1 | linear rebase, tracked-file-count guard, owned commit, push |

1. Lanes A–F start together with the frozen contract above.
2. C integrates only `cd600a18d06` or equivalent reviewed content; it must not
   import dirty files from the superseded stage1 worktree.
3. B–F finish all source/static work without waiting on A. They hand exact
   commands to A for execution on the admitted CLI.
4. A publishes the immutable CLI path and SHA once. Each owning lane runs its
   acceptance command once; unchanged green commands are never repeated.
5. F updates the matrix and manual-audit status from owner evidence; it never
   promotes static inspection, cached logs, simulation, or unavailable hardware.
6. H reviews every handoff. A failed criterion returns only to its owner for at
   most three fix/verify cycles.

### Bounded Stage 4 continuation

| TODO | Status | Implementation owner | Acceptance evidence |
|---|---|---|---|
| `HIR-BOOTSTRAP-NIL-001` | FAIL — fixes implemented, bootstrap unverified, three-check cap reached | compiler/bootstrap owner in a fresh session | `e331a5700ab`/HEAD `7a161abfabb` retains impl methods in the bootstrap accumulator and adds `bootstrap_impl_function_accumulation_spec.spl`. The final cycle-3 check reached `bootstrap-functions:count ... count=15`, completed wrapper/store/function-field access, then failed after `driver:errors-read:done`. The current typed-index `_driver_collect_hir_errors` change plus `hir_lowering_error_collection_spec.spl` addresses that localized boundary but has not been exercised by a post-fix bootstrap. |

The three-check cap is reached. No further Stage 4 retry is permitted this
session. In a fresh session, run exactly:

```bash
timeout -k 30s 3600s env SIMPLE_NO_STUB_FALLBACK=1 \
  scripts/bootstrap/bootstrap-from-scratch.sh \
  --backend=cranelift \
  --output=build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/full-bootstrap \
  --full-bootstrap --full-cli --no-mcp --jobs=4
```

Require a nonzero real-module bootstrap-function count, no error-collector nil
receiver, and wrapper exit 0. No full CLI was produced, so immutable CLI/core-C publication,
essential-tools and deliberate-red/empty-runner admission, focused font
execution, owner docgen, native promotion, and surface evidence remain
blocked.

The working tree additionally implements HIP-to-ROCm prepared-batch
canonicalization, fail-closed degenerate Simple Web results, ancestor-clipped
nested WM IMAGE projection, and a shared nested-frame collector whose behavioral
spec covers a valid reachable collection plus stale, duplicate, and orphan
rejection. Their direct specs are present, but none has authoritative execution
evidence; they remain active source changes.

## Required handoff format

Each lane reports:

1. owned files changed;
2. REQ/NFR rows addressed;
3. exact command, binary path/SHA, exit status, and authoritative markers;
4. retained evidence paths;
5. remaining blocker with prerequisite and resume command;
6. explicit confirmation that unrelated files and frozen interfaces were not changed.

## Merge and completion gates

- Clean isolated worktree; unrelated main-worktree changes untouched.
- No silent placeholder, fake device path, raw local runtime shortcut, or new dependency.
- `git diff --check`.
- `find doc/06_spec -name '*_spec.spl' | wc -l` equals `0`.
- Changed specs generate mirrored manuals with `0 stubs`.
- Focused deployed-runtime docgen covers all 32 changed/new specs; lane F reviews all 32
  retained `{out,err}` pairs but does not replace owner generation.
- `sh scripts/audit/direct-env-runtime-guard.shs --working` and `--staged`.
- Every REQ-001–015 and NFR-001–008 has current evidence or remains an explicit
  completion blocker; a blocked required row prevents overall `STATUS: PASS`.
- Independent final review runs once and owns all done marks.
- Before push: fetch/rebase linearly onto `origin/main`, compare tracked-file
  count before/after, commit only owned files, and push the isolated branch.
