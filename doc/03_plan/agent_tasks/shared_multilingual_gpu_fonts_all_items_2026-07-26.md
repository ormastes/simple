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
| GSUB/GPOS | reviewed completion is integrated on the isolated branch; superseded stage1 duplicates were not imported | execute the frozen shaping/parser specs on the admitted CLI |
| Bootstrap | `dd1d266dc9e` cleared the GPOS parse blocker; cached cycles 2 and 3 reached HIR but exited 132 on a nil receiver; cycle 3 ends after `compiler.spl` implementation methods with bootstrap function count zero; full CLI absent | stop this session at the three-cycle cap; diagnose the zero-count/nil boundary before a fresh-session retry |
| Focused tests | implementation and static coverage exist; prior runner exited before examples | calibrated, nonzero, authoritative runtime results |
| Native GPU | source/emission and partial backend evidence exist | one real 2D+3D promoted device route and current perf record |
| Surfaces | source contracts and retained artifacts exist | live canonical Web/GUI/WM/SimpleOS evidence and honest blocked rows |
| Docs/manuals | many drafts/history entries exist | current zero-stub manuals and one requirement/evidence matrix |

## Parallel lanes

| Lane | Owner | Exclusive writable scope | Deliverable and evidence |
|---|---|---|---|
| A bootstrap/runner | `bootstrap_runner` | bootstrap/compiler/runtime owner files required by the reproduced admission crash; `build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/**`; bootstrap bug/TODO docs | admitted Stage 4 CLI path+SHA, essential-tools smoke, deliberate-red/empty calibration, exact blocker after max 3 cycles |
| B manifests/distribution | `manifest_distribution` | font registry/assets/notices; release/package/SimpleOS font-manifest specs and mirrored manuals | REQ-001–005, NFR-001/003 executable byte/license/package evidence |
| C shaping/material/config | `shaping_material` | `src/lib/skia/feature/{glyph,shaper}/**`, canonical text-layout/font-renderer files, their unit specs | integrate GSUB/GPOS, exact selected-script shaping, shared batch/cache/config-policy evidence |
| D production surfaces | `surface_simpleos` | Web/GUI/WM/SimpleOS producer adapters and their dedicated system specs/manuals; no renderer internals | canonical Draw IR identity plus hosted and QEMU pixel/input evidence |
| E native 2D/3D/perf | `native_gpu_perf` | existing Engine2D/Engine3D native adapters, font native-readback/perf specs, retained native evidence | REQ-012/013 and NFR-002/004–008 real device proof or exact blocked-host contracts |
| F specs/docs/audit | `spec_docs_audit` | aggregate test plan, guides, state/traceability reports; no product code or owner-specific manuals | map every REQ/NFR, audit the frozen 26 owner-generated manuals/logs, and reject stale, missing, stubbed, or premature PASS evidence |
| H merge/final verify | `/root` | integration conflict resolution, final evidence report, branch history | primary review, direct-runtime guards, scoped verification once, status, rebase/file-count guard, push |

## Dependency and execution order

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
| `HIR-BOOTSTRAP-NIL-001` | FAIL — three-cycle cap reached | compiler/bootstrap owner in a fresh session | Commit `dd1d266dc9e` contains the GPOS block rewrite. Cached cycle 2 cleared parsing, reached HIR, and exited 132 on a nil receiver. Cycle 3 evidence is `build/native_probe/stage4-cycle3.log`, exit 132. Its last module is `src/compiler/backend/backend/compiler.spl`; all implementation methods, including `process_function`, complete lowering before `bootstrap-functions:count module=src/compiler/backend/backend/compiler.spl count=0` and the immediate `runtime error: field access on nil receiver`. Diagnose that boundary before authorizing any future retry. |

The three-cycle cap is reached. No further Stage 4 retry is permitted this
session. No full CLI was produced, so immutable CLI/core-C publication,
essential-tools and deliberate-red/empty-runner admission, focused font
execution, owner docgen, native promotion, and surface evidence remain
blocked.

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
- Frozen docgen ownership is B4+C13+D5+E4; lane F reviews all 26 retained
  `{out,err}` pairs but does not replace owner generation.
- `sh scripts/audit/direct-env-runtime-guard.shs --working` and `--staged`.
- Every REQ-001–015 and NFR-001–008 has current evidence or remains an explicit
  completion blocker; a blocked required row prevents overall `STATUS: PASS`.
- Independent final review runs once and owns all done marks.
- Before push: fetch/rebase linearly onto `origin/main`, compare tracked-file
  count before/after, commit only owned files, and push the isolated branch.
