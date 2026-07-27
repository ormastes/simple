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
| Runtime | no admitted current full CLI exists. The final bounded retained-Stage3 cycle cleared the NUL environment panic, then trapped at RIP `0x88034b` while its obsolete iterable collector passed a `LoweringError` with nil `span` to `_format_hir_lowering_error`; current source already contains the typed indexed collector, but that fix is absent from the executing producer | in a fresh verification window, P0 uses the Rust seed once as bootstrap-only authority to build current `bootstrap_main.spl` with `SIMPLE_NATIVE_ARENA_DECLS=1`, `SIMPLE_NO_STUB_FALLBACK=1`, and a fresh exclusive cache; that pure-Simple Stage2 rebuilds Stage3, which alone builds and admits the full CLI before A records its identity |
| Focused tests | implementation and static coverage exist; prior runner exited before examples | calibrated, nonzero, authoritative runtime results |
| Native GPU | source/emission and partial backend evidence exist | one real 2D+3D promoted device route and current perf record |
| Surfaces | source contracts and retained artifacts exist | live canonical Web/GUI/WM/SimpleOS evidence and honest blocked rows |
| Docs/manuals | 34 changed/new sources since `origin/main`; 14 mirrors missing, 20 stale, zero current, and zero retained docgen logs | regenerate all 34 mirrors with the admitted pure-Simple runtime, require `0 stubs`, and update one requirement/evidence matrix |

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
| A2 command calibration | `bootstrap_runner` | `build/test-artifacts/shared_multilingual_gpu_fonts/{essential-tools,runner-calibration}/**`, focused runner contract/manual, and immutable preflight evidence | A1 | essential-tools (including its lint/duplicate probes), deliberate-red, zero-example evidence, then one focused `test_runner_result_wrapper_spec.spl` preflight before B–E use the helper |
| B1 manifests/distribution | `manifest_distribution` | font registry/assets/notices, release/package/SimpleOS font-manifest code and specs | A2 | REQ-001–005 and NFR-001/003 executable byte/license/package evidence |
| B2 distribution manuals | `manifest_distribution` | only B-owned mirrored manuals and docgen logs | B1 | current `0 stubs` manuals for B's six changed specs |
| C1 shaping/material/config | `shaping_material` | `src/lib/skia/feature/{glyph,shaper}/**`, canonical text-layout/font-renderer files, their unit/aggregate specs | A2 | reviewed GSUB/GPOS, exact selected-script shaping, shared batch/cache/config-policy evidence |
| C2 shaping manuals | `shaping_material` | only C-owned mirrored manuals and docgen logs | C1 | current `0 stubs` manuals for C's 15 changed specs |
| D1 Engine2D capability | `surface_simpleos` | Engine2D production-route spec/manual only; no renderer internals | C1 | `engine2d_font_surface_verification_spec.spl` proves Draw IR text reaches the shared `FontRenderer` path |
| D2 Web capability | `surface_simpleos` | Web producer adapters and Web specs/manuals | D1 | canonical HTML/WebIR → Draw IR identity and visible result |
| D3 GUI capability | `surface_simpleos` | GUI producer adapters and GUI specs/manuals | D1 | widget scene → Draw IR identity and correlated input |
| D4 hosted-WM capability | `surface_simpleos` | hosted-WM producer adapter and dedicated spec/manual/evidence | D1 plus hosted display | canonical hosted frame, glyph crop, and correlated WM input |
| D5 x86 SimpleOS capability | `surface_simpleos` | x86 SimpleOS producer/spec/manual/QEMU evidence | D1 plus x86 QEMU | pinned guest bytes, framebuffer glyph pixels, and correlated QMP input |
| D6 RV64 SimpleOS capability | `surface_simpleos` | RV64 producer/spec/manual/QEMU evidence | D1 plus RV64 QEMU | pinned guest bytes, framebuffer glyph pixels, and VirtIO input |
| D7 surface manuals | `surface_simpleos` | only D-owned mirrored manuals and docgen logs | D2–D6 | current `0 stubs` manuals for D's ten changed specs, including the SimpleOS producer/consumer artifact-root contract; unavailable hosts remain blocked |
| E1 deterministic emission | `native_gpu_perf` | existing portable emitter/native adapter specs and retained compile artifacts | A2+C1 | versioned deterministic emission/compile evidence; no execution claim |
| E2 native 2D/3D | `native_gpu_perf` | existing Engine2D/Engine3D native adapters, native-readback spec, retained device evidence | D1+E1 plus real device | texture/upload/bind/draw/fence/device-origin readback for 2D and 3D |
| E3 native performance/manuals | `native_gpu_perf` | native-readback and performance specs/manuals plus retained device/perf evidence | E2 | current `0 stubs` manuals for E's two changed specs; NFR-002/004–008 fixture, p95, hit, CPU/GPU, RSS/VRAM, upload, device/driver record |
| F1 evidence/manual audit | `spec_docs_audit` | aggregate plan, guide, state/traceability reports; no product code or owner manuals | A2+B2+C2+D7+E3 | audit all 34 source/manual/log triples; reject missing, stale, stubbed, simulated, or premature PASS evidence |
| H1 final review | `/root` | integration conflict resolution and final evidence report | F1 | independently map REQ-001–016/NFR-001–008 and run final guards once |
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

P0 must use a fresh exclusive Stage2 cache because the retained cache was
produced by the obsolete Stage3. Later pure-Simple stages may preserve their
own isolated incremental caches. P0 must deliver a fresh current full CLI that
passes this exact admission before A starts:

The retained Stage3 SHA-256
`704f67af420bd8788dda809b46112d0a9a76cec64601ebfe2a6958a894aa380f`
must not be retried: it embeds the obsolete collector. In the next verification
window, P0 first produces a repaired pure-Simple Stage2 from current
`src/app/cli/bootstrap_main.spl` using the repo Rust seed only as bootstrap
authority, `SIMPLE_NATIVE_ARENA_DECLS=1`,
`SIMPLE_NO_STUB_FALLBACK=1`, runtime bundle `core-c-bootstrap`, and a new
exclusive `SIMPLE_NATIVE_BUILD_CACHE_DIR`. Stage2 must then rebuild Stage3.
Rust-seed output is never test, docgen, focused-run, or admission evidence.

Run the canonical producer once from the final pushed checkpoint; do not reuse
an output root:

```bash
set -euo pipefail
CHECKPOINT_SHA=<final-pushed-feature-sha>
ADMISSION_ROOT="/tmp/simple-font-cli-admission-$CHECKPOINT_SHA"
ADMISSION_TREE="$ADMISSION_ROOT/worktree"
test ! -e "$ADMISSION_ROOT"
mkdir -p "$ADMISSION_ROOT"
git worktree add --detach "$ADMISSION_TREE" "$CHECKPOINT_SHA"
(
  cd "$ADMISSION_TREE"
  SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_NATIVE_ARENA_DECLS=1 \
    sh scripts/bootstrap/bootstrap-from-scratch.sh \
      --backend=cranelift --output="$ADMISSION_ROOT/artifacts" \
      --full-bootstrap --mode=dynload --full-cli --fresh-cache --jobs=1 --no-mcp
)
CLI="$ADMISSION_ROOT/artifacts/full/x86_64-unknown-linux-gnu/simple"
test -x "$CLI"
```

The producer first creates the missing Rust bootstrap authority, then uses its
seed only for the recorded Stage2 build. The immutable admitted pure-Simple
Stage2 builds Stage3; the producer records both transcripts, source/runtime
snapshots, and manifest verification. `SIMPLE_NATIVE_ARENA_DECLS=1` is
hash-bound inside both the producer and its manifest replay; the outer binding
is only fail-safe clarity.

```bash
set -euo pipefail
CLI=/absolute/path/to/fresh/pure-simple
CLI_SHA=$(sha256sum "$CLI" | awk '{print $1}')
CORE_C_DIR=/absolute/path/to/matching/core-c
CORE_C_SHA=$(sha256sum "$CORE_C_DIR/libsimple_runtime.a" | awk '{print $1}')
ESSENTIAL_ROOT=build/test-artifacts/shared_multilingual_gpu_fonts/essential-tools
mkdir -p "$ESSENTIAL_ROOT"
SIMPLE_BINARY="$CLI" sh scripts/check/check-bootstrap-essential-tools-smoke.shs \
  >"$ESSENTIAL_ROOT/smoke.out" 2>"$ESSENTIAL_ROOT/smoke.err"
```

The essential-tools command must report
`essential_test_runner_smoke=true`, `essential_lint_smoke=true`,
`essential_duplicate_checker_smoke=true`, and
`bootstrap_essential_tools_smoke=true`. Its lint and duplicate probes are not
run a second time.

A2 then runs the hash-bound deliberate-red and zero-example calibration exactly
once:

```bash
set -euo pipefail
CAL=build/test-artifacts/shared_multilingual_gpu_fonts/runner-calibration
mkdir -p "$CAL"
if "$CLI" run src/app/test/font_evidence_runner.spl -- \
    "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA" \
    scripts/check/fixtures/font_evidence_runner_fail_spec.spl \
    >"$CAL/fail.out" 2>"$CAL/fail.err"; then
  fail_rc=0
else
  fail_rc=$?
fi
if "$CLI" run src/app/test/font_evidence_runner.spl -- \
    "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA" \
    scripts/check/fixtures/font_evidence_runner_empty_spec.spl \
    >"$CAL/empty.out" 2>"$CAL/empty.err"; then
  empty_rc=0
else
  empty_rc=$?
fi
[ "$fail_rc" -eq 1 ]
[ "$empty_rc" -eq 1 ]
```

The first log must contain `test-runner: spec failed`; the second must contain
`test-runner: no examples executed`. B–E reference this immutable calibration;
they do not rerun it. A2 next runs
`test/01_unit/lib/test_runner_result_wrapper_spec.spl` once through the
immutable focused helper in the verification report. That preflight must pass
before B–E use the helper.

## Production capability rows

| Task | Executable acceptance row | Required runtime result |
|---|---|---|
| D1 Engine2D | `test/03_system/app/simple_2d/feature/engine2d_font_surface_verification_spec.spl` | nonzero public Engine2D shared-font examples and readback oracle |
| D2 Web | `test/03_system/app/simple_web/feature/web_font_rendering_surface_spec.spl` | exact face/advance identity through WebIR and Draw IR, visible pixels/input |
| D3 GUI | `test/03_system/gui/feature/gui_font_event_surface_spec.spl` | widget identity through Draw IR and correlated event result |
| D4 hosted WM | `test/03_system/gui/linux_hosted_wm_live_window_spec.spl` | live canonical frame, glyph crop, and correlated WM event |
| D5 x86 SimpleOS | `test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl` | pinned guest hash, QEMU framebuffer glyph crop, and QMP input |
| D6 RV64 SimpleOS | `test/03_system/os/wm/rv64_simpleos_wm_font_input_spec.spl` | pinned guest hash, RV64 framebuffer glyph crop, and VirtIO input |

## Thirty-four-spec manual inventory

Owners generate their own manuals with the immutable docgen helper in the
verification report. A owns the focused runner contract, B owns six changed
specs, C owns 15, D owns ten, and E owns two. Fourteen mirrors are missing and
20 are stale. Hand edits do not count; every source requires current docgen
with `0 stubs`. F audits only after owner generation.

## Dependency rules

1. C integrates only `cd600a18d06` or equivalent reviewed content and never
   imports dirty superseded-stage1 files.
2. B owns manifests/staging, while D owns live SimpleOS production evidence.
3. C owns `FontRenderer`, batch/cache/config and aggregate material specs; D
   owns producer adapters; E owns native adapter/device/perf evidence.
4. Owners generate their manuals; F is audit-only. H alone edits final
   plan/state/report integration and branch history.
5. Each acceptance command runs once. A failure returns only to its owner for
   at most three fix/verify cycles; unchanged green commands are never repeated.

### Compiler-enablement boundary

Compiler/bootstrap behavior is not a font requirement and cannot promote a font
row. The current HirBlock, typed lowering-error collector, native-arena, and
direct-entry fixes are retained only because they are necessary to produce the
pure-Simple prerequisite. P0 remains a prerequisite artifact provider: Rust
seed use stops after Stage2 generation, while Stage3/full-CLI admission and all
font evidence use pure-Simple binaries.

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
- Focused deployed-runtime docgen covers all 34 changed/new specs; lane F
  reviews all 34 immutable command/output/error/exit/manual-hash sets but does
  not replace owner generation.
- `sh scripts/audit/direct-env-runtime-guard.shs --working` and `--staged`.
- Every REQ-001–016 and NFR-001–008 has current evidence or remains an explicit
  completion blocker; a blocked required row prevents overall `STATUS: PASS`.
- Independent final review runs once and owns all done marks.
- Before push: fetch/rebase linearly onto `origin/main`, compare tracked-file
  count before/after, commit only owned files, and push the isolated branch.

## 2026-07-27 evidence-graph correction

This current runbook supersedes the historical 32-manual/37-command accounting.
The authoritative scope is 34 manuals (14 missing, 20 stale) and 39 focused
commands: one runner preflight, B6, C17, D11, and E4. The added rows are the
focused runner contract and the SimpleOS producer/consumer artifact-root
contract. Historical log entries remain evidence of what was known when
recorded; they do not override this correction.
