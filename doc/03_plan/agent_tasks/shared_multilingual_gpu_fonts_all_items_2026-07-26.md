<!-- codex-design -->
# Shared Multilingual GPU Fonts — All Remaining Items

## Goal and authority

Requirements remain `doc/02_requirements/{feature,nfr}/shared_multilingual_gpu_fonts.md`
and cover REQ-001–016 plus NFR-001–008.
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
| GSUB/GPOS | the current source is a static implementation candidate with no superseded duplicate lane; REQ-006–010/015/016 remain runtime-unverified. REQ-011 is still blocked by the compatibility bitmap route | execute C18 once on the admitted runtime; route the REQ-011 compatibility removal/parity row to `surface_simpleos` |
| Runtime | pushed HEAD `502b70b5460` produced temporary Stage 2 successor3 at `build/native_probe/memory-dispatch-fix/stage2-goal-successor3-simple`, SHA-256 `dd7e747ad1e22bb71d46c5737d20d2d250146af70fdd3c621f66d7ab57ca26cf`, with `689 reused / 4 rebuilt`. Both Option gates then stopped in the pure in-process compiler with `field access on nil receiver` and SIGILL; the three-cycle cap is exhausted and no Stage 4 candidate exists | a fresh P0 session first diagnoses the Option root cause, then produces a current pure-Simple Stage 3 parent and one incremental Stage 4 full CLI. Stage 2 is diagnostic only; do not rerun the unchanged smoke or start a full bootstrap |
| Focused tests | the exact immutable graph is 46 commands: preflight 1 + B6 + C18 + D12 + E9. No current-runtime command has accepted evidence | after A admission/calibration, each owner runs its commands once and retains immutable command/stdout/stderr/exit receipts |
| Native GPU | the E audit leaves every native/performance row blocked; CPU/simulation diagnostics cannot promote a row, and no product edit is justified before real-device evidence exposes a concrete failure | one admitted real 2D+3D same-device route and current performance/device-loss receipts, or an explicit unavailable-host blocker |
| Surfaces | Web/GUI/WM/SimpleOS routing is statically valid through the frozen Draw IR/Engine2D owners; no live hosted/QEMU evidence exists | D12 executes once after admission; unavailable hosted, x86, RV64, or device rows stay blocked, never skipped/PASS |
| Docs/manuals | the authoritative changed-font manifest has 42 canonical pairs: 19 mirrors missing, 23 stale, zero current. Four canonical compiler-prerequisite mirrors are also missing. Diagnostic manuals under `build/` are noncanonical and cannot satisfy docgen | owners generate A1 + B6 + C17 + D11 + E7 canonical font manuals and the four prerequisite manuals with the admitted runtime and `0 stubs`; F audits the linked manifest |

The isolated branch and its remote are synchronized at pushed HEAD
`502b70b5460` (`0 ahead / 0 behind`). Without fetching, the recorded
`origin/main` is `dcc5328864d5`; HEAD is 82 commits ahead and 467 behind it.
AC-12 remains active until completion-time fetch, linear rebase, file-count
guard, and push.
Source-present but runtime-unverified work at that checkpoint includes the one-pass package sibling index, positional Stage 3
build with target/cache/thread/runtime forwarding, reviewed GSUB/GPOS coverage,
GPOS VariationIndex long-word handling, fail-closed degenerate Web results,
HIP prepared-batch canonicalization, and nested-WM clipping/stale-frame checks.
Current Stage3/HIR source also hoists environment/profile decisions once per
compiler invocation, avoiding per-expression reads and diagnostic construction.

The 2026-07-28 continuation additionally fixes PairPos format-1 owner-relative
Device/VariationIndex lookup, native-safe staged transfer for every Engine2D and
Engine3D text/glyph production path, typed selected-font skip rejection in the
SimpleOS executor, honest hosted-WM compatibility provenance, Draw IR SDN font
identity/advance round-trip coverage, and fail-closed native/performance
evidence identity. The completed owner overlay also uses scalar `i64` fault
codes/masks/sequences and device-loss sequences on native paths, retains
post-fault identity and committed CPU-fallback counts, makes atlas replacement
and incomplete-completion cleanup transactional, and reuses caller-owned
plan/batch, projection, and vertex-byte scratch storage, bounds the reusable
completed vertex pool, retains only one deferred-fallback snapshot, and clears
Engine2D fallback pixels after use. These are current-source changes only until
the admitted runtime executes them. The 42 font manuals and four
compiler-prerequisite manuals still require admitted docgen with `0
stubs`; no runtime, docgen, native, QEMU, or performance row has run.

Host-independent Rust diagnostics pass: the exact runtime UUID/LUID identity
test completed in 0.00s at 5,632 KiB max RSS, and the exact compiler
device-loss classification test completed in 17.84s at 2,169,768 KiB max RSS.
They remain diagnostics, not pure-Simple acceptance evidence.

## Current owner overlay — 2026-07-29 remade schedule

| Completed audit lane | Audited result | Next owner / writable authority |
|---|---|---|
| `runtime_admission_audit10` | successor3 provenance is valid diagnostic evidence; both Option gates nil/SIGILL, the cap is exhausted, and no Stage 4 exists | `/root` as P0 in a fresh bounded session; compiler/runtime root-cause files and isolated producer artifacts only |
| `manifest_audit10` | B source is complete; execution and all six B docgens remain blocked on A admission | `manifest_distribution` after A2; no source edit unless the first authoritative failure identifies one |
| `shaping_audit10` | C is a static implementation candidate with no duplicate GSUB/GPOS lane; REQ-011 remains blocked by the compatibility bitmap route | `shaping_material` owns C18 execution/C17 manuals; `surface_simpleos` owns the REQ-011 compatibility row |
| `surface_audit10` | D routing is statically valid through canonical Draw IR/Engine2D owners; live hosted/QEMU evidence is absent | `surface_simpleos` owns D12 execution/D11 manuals and retains unavailable rows as blocked |
| `native_perf_audit10` | all E rows remain blocked; no product edit is justified from static evidence | `native_gpu_perf` owns E9 execution/E7 manuals only after admitted runtime and real-device prerequisites exist |
| `manual_inventory_audit10` | 42 font pairs = 19 missing + 23 stale + 0 current; four compiler-prerequisite mirrors are missing; build-tree manuals are diagnostic/noncanonical | A/B/C/D/E owners generate; `spec_docs_audit` audits the [authoritative manifest](../../../09_report/shared_multilingual_gpu_fonts_all_items_verification.md#canonical-executablemanual-audit) |
| `/root` | merge owner and highest-capability final reviewer | integrates bounded handoffs, owns done marks, final guards, rebase, and push |

### Current focused source-contract ownership

These are source lanes, not permission to execute in this exhausted producer
window. After a future admitted CLI/core-C identity exists, `/root` runs each
focused command once through the frozen `run_focused_spec` helper. All command,
stdout, stderr, and exit receipts remain under
`build/test-artifacts/shared_multilingual_gpu_fonts/focused/attempt-$FOCUSED_ATTEMPT/`.

| Owner | Writable source/test scope | Queued focused source-contract command | Dependency | Final reviewer |
|---|---|---|---|---|
| `font_native_perf_audit` | Simple-side stable physical-device identity propagation through the existing Engine2D Vulkan session/backend, Vulkan3D backend/adapter, native-readback/perf helper/spec, plus performance-evidence, backend-fault, and device-metadata source contracts; no Rust runtime identity or synchronization implementation | `run_focused_spec test/01_unit/helpers/shared_multilingual_gpu_fonts_perf_evidence_spec.spl`; `run_focused_spec test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spec.spl`; `run_focused_spec test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_session_device_metadata_spec.spl`; then `run_focused_spec test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl` | source-present runtime identity facade, admitted CLI/core-C, and one discrete/integrated Vulkan device; the native command remains blocked until all runtime dependencies exist | `/root` |
| `font_surface_audit` | Engine2D scalar owner-fault receipt and scratch-reuse source contract | `run_focused_spec test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_font_scalar_receipt_spec.spl` | future fresh producer window and admitted CLI/core-C | `/root` |
| `font_matrix_audit` | hosted-WM live-proof focus/provenance source contract | `run_focused_spec test/01_unit/os/hosted/hosted_entry_live_proof_focus_contract_spec.spl` | future fresh producer window and admitted CLI/core-C | `/root` |
| `stage3_hir_lifetime` | Vulkan runtime selected-device identity plus fence-wait/wait-idle last-error retention, runtime symbol/codegen/interpreter wiring, canonical `std.*.io.vulkan_sffi` facades, and source assertions in `test/01_unit/lib/gpu/engine3d/font_hud_material_spec.spl`; no Engine2D/Engine3D evidence-record ownership | `run_focused_spec test/01_unit/lib/gpu/engine3d/font_hud_material_spec.spl` | future fresh producer window and admitted CLI/core-C; runtime execution remains blocked in this window | `/root` |

No audit promotes a runtime-dependent requirement or unavailable capability.
Every unavailable host/device row remains blocked, and final requirement/AC
counts are regenerated only from current owner evidence.

## Prior owner overlay (superseded by the continuation)

| Current sidecar | Exact scope | Status / writable authority |
|---|---|---|
| `process_rule_fix` / `bootstrap_rule_crosscheck` | incremental/full-bootstrap policy correction and crosscheck | source-complete / PASS; policy files only |
| `pure_cli_inventory` / `incremental_cache_audit` | eligible current CLI, parent, and cache provenance | complete: none eligible; N/A — read-only |
| `remaining_source_gaps` | REQ/NFR implementation/source coverage | PASS; N/A — read-only |
| `compiler_perf_source_audit` | Stage4 hot-path profiling audit | complete: three shared root causes identified |
| `low_memory_forward_fix` | focused Stage4 low-memory forwarding/restoration | source-complete, runtime-unverified |
| `sibling_symbol_index_fix` | one direct package-sibling owner index per lowering pass | source-complete, runtime-unverified |
| `qualified_function_index_fix` | direct qualified-function lookup index | source-complete, runtime-unverified |
| `low_memory_review` / `sibling_index_review` / `qualified_index_review` | independent focused review | PASS; N/A — read-only |
| `perf_fix_docs` / `perf_manual_inventory` | architecture, blocker truth, and three-spec mirror audit | complete; three canonical prerequisite mirrors missing |
| `final_perf_review` / `static_guard_review` | combined correctness and policy review | PASS; N/A — read-only |
| `/root` | merge owner and final high-capability reviewer | integration, final guards, sync/push |

The former B–F implementation aliases below are decomposition history, not
additional active writers in this checkpoint. Their product-code lanes are N/A
unless `/root` assigns a concrete failed acceptance row after CLI admission.

## Parallel lane decomposition

| Lane | Owner | Exclusive writable scope | Deliverable and evidence |
|---|---|---|---|
| A bootstrap/runner | `bootstrap_runner` | bootstrap/compiler/runtime owner files required by the reproduced admission crash; `build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/**`; bootstrap bug/TODO docs | admitted Stage 4 CLI path+SHA, essential-tools smoke, deliberate-red/empty calibration, exact blocker after max 3 cycles |
| B manifests/distribution | `manifest_distribution` | font registry/assets/notices; release/package/SimpleOS font-manifest specs and mirrored manuals | REQ-001–005, NFR-001/003 executable byte/license/package evidence |
| C shaping/material/config | `shaping_material` | `src/lib/skia/feature/{glyph,shaper}/**`, canonical text-layout/font-renderer files, their unit specs | integrate GSUB/GPOS, exact selected-script shaping, shared batch/cache/config-policy evidence |
| D production surfaces | `surface_simpleos` | Web/GUI/WM/SimpleOS producer adapters and their dedicated system specs/manuals; no renderer internals | canonical Draw IR identity plus hosted and QEMU pixel/input evidence |
| E native 2D/3D/perf | `native_gpu_perf` | existing Engine2D/Engine3D native adapters, font native-readback/perf specs, retained native evidence | REQ-012/013 and NFR-002/004–008 real device proof or exact blocked-host contracts |
| F specs/docs/audit | `spec_docs_audit` | aggregate test plan, guides, state/traceability reports; no product code or owner-specific manuals | map every REQ/NFR, audit the [authoritative 42-pair manifest](../../../09_report/shared_multilingual_gpu_fonts_all_items_verification.md#canonical-executablemanual-audit) and owner logs, and reject stale, missing, build-tree-only, stubbed, or premature PASS evidence |
| H merge/final verify | `/root` | integration conflict resolution, final evidence report, branch history | primary review, direct-runtime guards, scoped verification once, status, rebase/file-count guard, push |

| Task | Owner | Exclusive writable scope | Dependency | Deliverable and evidence |
|---|---|---|---|---|
| P0 current-source pure-CLI admission | `/root` (fresh producer window only) | future detached current checkpoint, unique incremental cache/output, admission logs, and retained `build/native_probe/` cache/profile artifacts; no font product-code edits | successor3 `dd7e747a...26cf` is diagnostic only; both Option gates nil/SIGILL and the three-cycle cap is exhausted. First make a root-cause change in a fresh session, then produce current Stage 3 and incremental Stage 4 | current-source pure-Simple full CLI plus CLI/core-C paths and SHA-256 identities; essential-tools smoke PASS; no unchanged Option rerun, Rust-seed acceptance, or full bootstrap |
| A1 runtime identity | `bootstrap_runner` | retained runtime identity and focused runner artifacts only | P0 | immutable admitted CLI/core-C identity; reject Rust seed and stale binaries |
| A2 command calibration | `bootstrap_runner` | `build/test-artifacts/shared_multilingual_gpu_fonts/{essential-tools,runner-calibration}/**`, focused runner contract/manual, and immutable preflight evidence | A1 | essential-tools (including its lint/duplicate probes), deliberate-red, zero-example evidence, then one focused `test_runner_result_wrapper_spec.spl` preflight before B–E use the helper |
| B1 manifests/distribution | `manifest_distribution` | font registry/assets/notices, release/package/SimpleOS font-manifest code and specs | A2 | REQ-001–005 and NFR-001/003 executable byte/license/package evidence |
| B2 distribution manuals | `manifest_distribution` | only B-owned mirrored manuals and docgen logs | B1 | current `0 stubs` manuals for B's six changed specs |
| C1 shaping/material/config | `shaping_material` | `src/lib/skia/feature/{glyph,shaper}/**`, canonical text-layout/font-renderer files, their unit/aggregate specs | A2 | reviewed GSUB/GPOS, exact selected-script shaping, shared batch/cache/config-policy evidence |
| C2 shaping manuals | `shaping_material` | only C-owned mirrored manuals and docgen logs | C1 | current `0 stubs` manuals for C's 17 changed specs |
| D1 Engine2D capability | `surface_simpleos` | Engine2D production-route spec/manual only; no renderer internals | C1 | `engine2d_font_surface_verification_spec.spl` proves Draw IR text reaches the shared `FontRenderer` path |
| D2 Web capability | `surface_simpleos` | Web producer adapters and Web specs/manuals | D1 | canonical HTML/WebIR → Draw IR identity and visible result |
| D3 GUI capability | `surface_simpleos` | GUI producer adapters and GUI specs/manuals | D1 | widget scene → Draw IR identity and correlated input |
| D4 hosted-WM capability | `surface_simpleos` | hosted-WM producer adapter and dedicated spec/manual/evidence | D1 plus hosted display | canonical hosted frame, glyph crop, and correlated WM input |
| D5 x86 SimpleOS capability | `surface_simpleos` | x86 SimpleOS producer/spec/manual/QEMU evidence | D1 plus x86 QEMU | pinned guest bytes, framebuffer glyph pixels, and correlated QMP input |
| D6 RV64 SimpleOS capability | `surface_simpleos` | RV64 producer/spec/manual/QEMU evidence | D1 plus RV64 QEMU | pinned guest bytes, framebuffer glyph pixels, and VirtIO input |
| D7 surface manuals | `surface_simpleos` | only D-owned mirrored manuals and docgen logs | D2–D6 | current `0 stubs` manuals for D's eleven changed specs, including the hosted focus contract and SimpleOS producer/consumer artifact-root contract; unavailable hosts remain blocked |
| E1 deterministic emission | `native_gpu_perf` | existing portable emitter/native adapter specs and retained compile artifacts | A2+C1 | versioned deterministic emission/compile evidence; no execution claim |
| E2 native 2D/3D | `native_gpu_perf` | existing Engine2D/Engine3D native adapters, native-readback spec, retained device evidence | D1+E1 plus real device | texture/upload/bind/draw/fence/device-origin readback for 2D and 3D |
| E3 native performance/manuals | `native_gpu_perf` | native-readback and performance specs/manuals plus retained device/perf evidence | E2 | current `0 stubs` manuals for E's seven changed specs; NFR-002/004–008 fixture, p95, hit, CPU/GPU, RSS/VRAM, upload, device/driver record |
| F1 evidence/manual audit | `spec_docs_audit` | aggregate plan, guide, state/traceability reports; no product code or owner manuals | A2+B2+C2+D7+E3 | audit the [authoritative 42 source/manual manifest](../../../09_report/shared_multilingual_gpu_fonts_all_items_verification.md#canonical-executablemanual-audit) and owner logs; reject missing, stale, diagnostic-build-tree-only, stubbed, simulated, or premature PASS evidence |
| H1 final review | `/root` | integration conflict resolution and final evidence report | F1 | independently map REQ-001–016/NFR-001–008 and run final guards once |
| H2 sync/push | `/root` | branch history only | H1 | linear rebase, tracked-file-count guard, owned commit, push |

1. The six read-only audit lanes above are complete; they create no done marks.
2. P0 resumes only in a fresh bounded session after a root-cause change; it
   publishes one immutable current CLI/core-C identity after admission.
3. B has no static source gap. C is a static candidate; only the REQ-011
   compatibility route is assigned to D. E has no justified product edit before
   authoritative native execution.
4. After A2, owners run preflight 1 + B6 + C18 + D12 + E9 exactly once.
5. Owners generate A1 + B6 + C17 + D11 + E7 manuals; F audits the linked
   manifest and never accepts build-tree manuals, simulation, or unavailable
   hardware.
6. H reviews every handoff. A failed criterion returns only to its owner for at
   most three fix/verify cycles; unavailable rows remain blocked.

### Historical Stage 4 evidence and current admission rule

| TODO | Status | Implementation owner | Acceptance evidence |
|---|---|---|---|
| `HIR-BOOTSTRAP-NIL-001` | FAIL — source fixes present at `269f46387e1`, runtime unverified, three-check cap reached | N/A in this verification window | Historical `e331a5700ab`/`7a161abfabb` retained impl accumulation; cycle 3 reached `bootstrap-functions:count ... count=15`, completed wrapper/store/function-field access, then its obsolete iterable collector trapped at RIP `0x88034b` while formatting a nil-span `LoweringError`. Current source retains the typed indexed collector and adds one shared package sibling index; neither has authoritative current-runtime evidence. |

External stale-source Stage4 `c167e250` ended `EXIT=143`/`SIGTERM` with no full
output; its log SHA-256 is
`5a49ab01a7f7db6fc112c77c605c4760ff1a68f6929e5cf1e7037deef8d1c1d7`.
Its stale Stage3 `01ef253d...3c3c7` records
`full_cli_status=separate-not-proven` and is historical only, not an eligible
parent. The earlier retained Stage3 SHA-256
`704f67af420bd8788dda809b46112d0a9a76cec64601ebfe2a6958a894aa380f`
must not be retried: it embeds obsolete source. The final current-source
producer attempt also produced no candidate, so **no fourth producer or full
bootstrap is permitted in this verification window**.

P0 may resume in a future verification window only when an independently owned
pure-Simple parent completes successfully. `/root` first retains its exit
record, transcript, source
checkpoint, and SHA without signalling or adopting its worktree. If those
prove a real pure-Simple binary, that immutable parent runs one incremental
native build from this isolated working overlay rooted at `24a77be3c89a`, with
a new output root and exclusive cache, to compile current
`src/app/cli/main.spl`. Before starting, require the tracked `src scripts test`
binary-diff SHA-256
`c5233e73b817e1ca915aa768f62856200b7fc43b542b2715d03ed7c5eab218b1`
and the untracked `src/lib/common/gpu/font_owner_fault_receipt.spl` SHA-256
`032978d4654af8011f0d0bd084119dc7ed035bf8710d03c6928318c56a33817b`.
Only the resulting current-source binary may enter the admission, smoke,
calibration, focused-test, or docgen gates below. A Rust seed, stale Stage 3,
old detached checkpoint, or the external parent's older-source binary is never
acceptance evidence.

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

## Forty-two-spec manual inventory

Owners generate their own manuals with the immutable docgen helper in the
verification report. Exact ownership is A1 + B6 + C17 + D11 + E7. The
[authoritative manifest](../../../09_report/shared_multilingual_gpu_fonts_all_items_verification.md#canonical-executablemanual-audit)
contains 19 missing mirrors, 23 stale mirrors, and zero current canonical
manuals. Four compiler-prerequisite mirrors are also missing. Static cleanup of
nine boolean matcher wrappers and four production-surface step-vocabulary
violations is source-complete and independently reviewed PASS, but remains
runtime-unverified. Hand edits and diagnostic manuals under `build/` do not
count; every source requires current canonical docgen with `0 stubs`. F audits
only after owner generation.

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
pure-Simple prerequisite. P0 is owned by `/root` for a future fresh producer
window only. Temporary successor3 at
`build/native_probe/memory-dispatch-fix/stage2-goal-successor3-simple`
(`dd7e747ad1e22bb71d46c5737d20d2d250146af70fdd3c621f66d7ab57ca26cf`,
`689 reused / 4 rebuilt`) remains diagnostic: both Option gates trap on a nil
receiver with SIGILL, the three-cycle cap is exhausted, and no Stage 4 exists.
A fresh window must make a root-cause change before another Option gate, produce
a current Stage 3 parent, and then use the documented incremental Stage 4 route.
The Rust seed, Stage 2, stale parents, and full bootstrap are not acceptance
evidence. All font evidence uses the admitted current-source pure-Simple binary.

P0 retains cache/profile history under `build/native_probe/`, including
`stage3-importfix-cache/`, `rebased-stage4-cycle3-final.log`, and
`lazy-sibling-stage3-cycle3-pure/build.log`. These are resume inputs and blocker
evidence, not authorization to execute the conditional command in this
exhausted window. `/root` remains the final reviewer.

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
- Focused deployed-runtime docgen covers all 42 changed/new specs; lane F
  reviews all 42 immutable command/output/error/exit/manual-hash sets but does
  not replace owner generation.
- Separate prerequisite docgen covers the four changed compiler perf-repair
  specs outside the font graph; all four mirrors must be current with
  `0 stubs` (all four canonical mirrors are currently missing).
- `sh scripts/audit/direct-env-runtime-guard.shs --working` and `--staged`.
- The admitted pure-Simple runtime checks `src/compiler`, `src/lib`,
  `src/app/mcp`, and `src/app/simple_lsp_mcp`, then runs
  `test/02_integration/app/mcp_stdio_integration_spec.spl` in interpreter mode.
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

C17 is exactly:

1. `shared_font_shaping_acceptance_spec.spl`
2. `shared_font_surfaces_spec.spl`
3. `ot_layout_apply_spec.spl`
4. `ot_layout_gsub_full_spec.spl`
5. `ot_layout_gpos_spec.spl`
6. `ot_layout_gpos_full_spec.spl`
7. `ot_layout_gpos_variation_spec.spl`
8. `ot_layout_lookup_flags_spec.spl`
9. `ot_layout_pinned_inventory_spec.spl`
10. `ot_parser_layout_selector_spec.spl`
11. `ot_parser_spec.spl`
12. `shaper_spec.spl`
13. `selected_devanagari_spec.spl`
14. `selected_arabic_spec.spl`
15. `font_renderer_spec.spl`
16. `font_render_config_spec.spl`
17. `font_compat_spec.spl`

The four rows omitted by the obsolete graph were `ot_layout_gsub_full`,
`ot_layout_gpos_full`, `ot_layout_gpos_variation`, and
`ot_layout_lookup_flags`. Overall verification remains **STATUS: FAIL** until
an admitted CLI executes the immutable 39-command graph, regenerates all 34
font manuals, and regenerates the three prerequisite perf-repair manuals, with
unavailable device/host rows retained as explicit blockers.

## 2026-07-28 current overlay inventory correction

This current correction supersedes the 34/39 accounting above. Seven retained
source-contract specs first expanded docgen to 41 manuals: four new missing
mirrors (`engine2d_font_scalar_receipt`, `vulkan_session_device_metadata`,
`font_compat`, and `font_hud_material`) plus three existing stale mirrors
(`shared_multilingual_gpu_fonts_perf_evidence`, `backend_vulkan_font`, and
`hosted_entry_live_proof_focus_contract`). The later Engine2D
`font_runtime_config` contract raises the current result to 42 manuals: 19
missing, 23 stale, and zero current.

Six focused executions are added because `font_compat_spec.spl` was already in
C17: the performance-evidence helper, Engine2D backend-fault contract,
Engine2D scalar-receipt contract, Vulkan device-metadata contract, Engine3D
HUD/material contract, and hosted focus/provenance contract. The added
`font_runtime_config` execution raises C to 18. The authoritative graph is
therefore 46 commands: preflight, B6, C18, D12, and E9. Every added
command uses the existing immutable focused-attempt root and `/root` reviewer;
no runtime command or docgen has run.
