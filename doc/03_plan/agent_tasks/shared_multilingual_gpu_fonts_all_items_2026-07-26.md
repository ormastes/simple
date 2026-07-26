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
| Bootstrap | deployed/runtime candidates have crashed or failed admission; no fresh Stage 4 PASS | fresh admitted full CLI plus essential-tools smoke |
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
| `ENUM-DISC-001` | FAIL — implementation in progress; evidence not admitted | compiler/bootstrap owners, then lane A for bootstrap only | Add full explicit discriminant propagation through parser, flat AST, bridge/typed `Variant`, and HIR/MIR lowering. Required focused coverage includes parser, bridge, and lowering specs; it must prove a literal non-sequential enum, the actual `SyscallId` source, exact `Exit=0`, `Mmap=10`, `IpcSend=20`, `Rename=44`, and implicit-after-explicit behavior. Concurrent source/test changes are work in progress, not current PASS evidence. |

The bounded order is: focused parser/HIR/MIR tests once; one
cache-preserving Stage 4 retry using the existing full-bootstrap output tree;
and, only after exit 0, immutable CLI/core-C hashes, essential-tools smoke, and
deliberate-red/empty-runner admission. Focused font execution follows
admission. Owner docgen follows passing runtime specs; lane F only audits it.
No generated manual is admitted before the CLI.

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
