# Shared Multilingual GPU Fonts — All-Items Verification

Date: 2026-07-26
Authority: selected requirements and NFRs in
`doc/02_requirements/{feature,nfr}/shared_multilingual_gpu_fonts.md`
Final done-mark owner: highest-capability `/root`

## Result

`STATUS: FAIL`

This is the current all-lane audit at HEAD `7a161abfabb` plus the current
working changes, not a runtime or native PASS. Static source and executable
coverage is broad, but no fresh pure-Simple full CLI has been admitted. The
continuation admitted bootstrap Stage 2 and Stage 3 for stage progression,
parsed the prior `SyscallId` enum blocker successfully, and cleared the
GPOS-data block-form parse error. `e331a5700ab`, integrated as HEAD
`7a161abfabb`, fixed impl-only bootstrap function accumulation. The final
cycle-3 Stage 4 check then localized the remaining nil receiver inside the HIR
error collector. The typed-index collector fix and its direct regression are
implemented in the working tree but bootstrap-unverified. Those stage
compilers are not a full font-test CLI.
The retained history and resume contract are in
`doc/08_tracking/bug/shared_font_stage4_stale_compiler_backfill_2026-07-26.md`.
Consequently runner calibration, focused execution, zero-stub docgen, native
promotion, QEMU pixels, and performance remain unaccepted.

### Current bootstrap blocker

- Stage 2:
  `build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/full-bootstrap/stage2/x86_64-unknown-linux-gnu/simple`,
  SHA-256
  `63523bc1f33c4705512279d126b1083b75296982699c5d51ca8d65b586b5b0ea`.
- Stage 3:
  `build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/full-bootstrap/stage3/x86_64-unknown-linux-gnu/simple`,
  SHA-256
  `efe455723c76643c327312292769262f0a9326d91d424773e11d45611742103b`.
  Both stages passed their sanity gates at commit `033c0f9e6ae`; commit
  `dd1d266dc9e` then rewrote the GPOS block form.
- Stage 4/full CLI is absent. Cached cycle 2 cleared parsing, reached HIR, and
  exited 132 on a nil receiver.
- The retained pre-fix log showed that
  `src/compiler/backend/backend/compiler.spl` completed all fifteen impl
  methods but published zero accumulated functions. `e331a5700ab`/HEAD
  `7a161abfabb` adds impl methods to the bootstrap accumulator and adds direct
  0+2/1+2 no-drop/no-duplication coverage.
- The final cycle-3 check reached
  `bootstrap-functions:count module=src/compiler/backend/backend/compiler.spl count=15`,
  completed constructor, wrapper, module-store, and functions-field markers,
  then failed immediately after `driver:errors-read:done`. This localizes the
  nil receiver inside `_driver_collect_hir_errors`.
- The current working change uses a typed indexed `LoweringError` loop and adds
  `hir_lowering_error_collection_spec.spl` for empty, recovered, and fatal
  arrays. It has not been exercised by a post-fix bootstrap.

No Stage 4 CLI/core-C identity was published and no global runner calibration
ran. The three-check cap is reached; no further retry is permitted this
session. A fresh session must verify the integrated accumulator and typed-index
collector before any downstream evidence can be accepted.

| Open TODO | Status | Required evidence before retry | Bounded continuation |
|---|---|---|---|
| `HIR-BOOTSTRAP-NIL-001` | FAIL — fixes implemented, bootstrap unverified, three-check cap reached | Verify `compiler.spl` retains its 15 impl methods and `_driver_collect_hir_errors` handles typed empty/recovered/fatal arrays without a nil receiver | No further retry this session. In a fresh session, run the exact bounded command below. Only exit 0 may unlock immutable CLI/core-C identity, essential-tools smoke, direct HIR specs, and deliberate-red/empty-runner gates; all downstream work stays blocked. |

## Requirement matrix

Every non-pass row names its owner, dependency, exact acceptance surface, and
final reviewer. `active` means the owning parallel lane can still change the
row; `blocked` means the required runtime/device evidence is unavailable.
Current count: `0 pass`, `14 active`, `9 blocked`.

| Row | Status | Owner / writable scope | Current executable and manual evidence | Dependency and exact completion command | Final reviewer |
|---|---|---|---|---|---|
| REQ-001 | active | B manifest/distribution | `shared_font_manifest_spec.spl` and mirror cover pins, order, totals, boundary | deployed pure-Simple runtime; run B command set below | `/root` |
| REQ-002 | active | B manifest/distribution | same pair covers decimal contribution, alias policy, deterministic regeneration | deployed pure-Simple runtime; run B command set | `/root` |
| REQ-003 | active | B+C manifest/shaping | manifest and shaping acceptance pairs cover sparse states and fail-closed cells | deployed pure-Simple runtime; run B and C command sets | `/root` |
| REQ-004 | active | B manifest/distribution | manifest, asset-manifest, installer, archive, SimpleOS bundle/staging specs exist; mirrors exist for the acceptance pairs | deployed pure-Simple runtime; run B command set and zero-stub docgen | `/root` |
| REQ-005 | active | B manifest/distribution | manifest and SimpleOS bundle specs cover the pinned candidate catalog and unchanged bytes | deployed pure-Simple runtime; run B command set | `/root` |
| REQ-006 | active | C+D shaping/surfaces | `shared_font_surfaces_spec.spl` and legacy Web/GUI/WM route pair cover the shared owner/material seam | deployed pure-Simple runtime; run aggregate and D command sets | `/root` |
| REQ-007 | active | C shaping/material | shaping acceptance plus selected Arabic/Devanagari and six integrated GSUB/GPOS unit specs exist; selected-memory binding rejects unregistered paths and path/hash mismatches, and GPOS catalog lookup now rejects duplicate indices without publishing partial adjustments | source is present but runtime-unverified; run the C command set on the deployed pure-Simple runtime and generate six missing unit mirrors | `/root` |
| REQ-008 | active | B+C manifest/shaping | manifest and parser/loader specs cover `glyf`, default instance, bitmap, and rejection policy | deployed pure-Simple runtime; run B/C command sets | `/root` |
| REQ-009 | active | C+E material/native | renderer, aggregate surface, emission, backend and perf specs contain cache identity/lifecycle oracles | deployed pure-Simple runtime and native record; run C/E sets | `/root` |
| REQ-010 | active | E native/emission | GPU emission and CUDA handoff executable/manual pairs cover source/artifact contracts; emission is not execution | deployed pure-Simple runtime; run E source commands; retained native artifact required for promotion | `/root` |
| REQ-011 | active | D+E surfaces/native | aggregate surfaces/route plus the six production capability rows below exist; working changes add fail-closed degenerate Web status, ancestor-clipped nested IMAGE projection, trait/concrete-pixel-buffer and Draw IR/Engine2D clip parity, full-buffer no-nesting parity, and shared nested-collector cases for valid collection plus stale/duplicate/orphan rejection | changes are source-present but runtime-unverified; deployed pure-Simple runtime, hosted frame and QEMU pixels required; complete all six rows below | `/root` |
| REQ-012 | blocked | E native 2D/3D/perf | native readback source contains HUD/world, handles, submit, fence, depth/transform and readback gates; working source also records durable successful atlas/vertex upload counts and byte totals and requires all four receipts for 3D promotion | source changes are runtime-unverified; deployed pure-Simple runtime plus real graphics device required; run E native command | `/root` |
| REQ-013 | blocked | E native 2D/3D/perf | native readback source rejects unavailable and forged promotion and now fails promotion closed when durable 3D upload receipts are missing | one real backend must pass both 2D and 3D through E native command | `/root` |
| REQ-014 | blocked | B–E generation / F audit | among 32 changed/new specs, 13 mirrors are missing, 19 are stale, zero are current, and no retained log proves `0 stubs` | deployed pure-Simple runtime; run all 32 docgen commands below; review manuals | `/root` |
| REQ-015 | active | C shaping/material/config | aggregate surfaces and focused config specs cover identity, policies, target order and pre-mutation rejection; working changes canonicalize HIP to ROCm on the prepared batch | batch change is unverified; deployed pure-Simple runtime required; run aggregate/C commands | `/root` |
| REQ-016 | active | I–N full OpenType layout | source integration covers GSUB 1–8, GPOS 1–9, LookupFlag/GDEF filtering, FeatureVariations, Device/VariationIndex and anchors, named context/data facades, nested contextual remaps, ppem/coordinates/LangSys, pixel/design-unit separation, and fail-closed selected preprocessing; focused regressions cover the reviewed P1s | execute all focused specs on an admitted pure-Simple CLI and regenerate/review all affected manuals | `/root` |
| NFR-001 | active | B manifest/distribution | manifest and SimpleOS bundle source gates cover immutable hashes, deterministic generation and corruption rejection | deployed pure-Simple runtime; run B command set | `/root` |
| NFR-002 | blocked | E native/perf | native readback and perf specs define exact packed-ARGB comparator and provenance fields | deployed pure-Simple runtime plus real device; run E native/perf commands | `/root` |
| NFR-003 | active | B manifest/distribution | manifest/bundle gates encode the 80 MiB and SimpleOS projection limits | deployed pure-Simple runtime; run B command set | `/root` |
| NFR-004 | blocked | E native/perf | performance spec and manual define warm hit and 1080p/4K p95 thresholds | real device must create a valid `build/shared_multilingual_gpu_fonts_perf/evidence.env` | `/root` |
| NFR-005 | blocked | E native/perf | performance spec defines equal-semantics 4,096-glyph CPU/GPU comparison | real promoted backend must prove at least 1.25x using E perf command | `/root` |
| NFR-006 | blocked | E native/perf | performance spec defines unchanged upload, RSS delta and GPU high-water checks | real device plus isolated RSS probe; run E perf command | `/root` |
| NFR-007 | blocked | E native/perf | native/perf specs define corrupt/device-loss fallback and unchanged identity/p95 checks | retained native fault-injection execution required | `/root` |
| NFR-008 | blocked | E native/perf | native/perf records require shaping through readback/resource stages; working 3D source adds successful atlas/vertex upload count and byte receipts | retained nonzero upload receipts, handles, fence and device-origin readback required | `/root` |

### REQ-011 production capability rows

The Engine2D row is the shared prerequisite; the other five rows are independent
after it passes. The synced checkout contains no retained current runtime
artifacts at the paths below, so source inspection cannot promote any row.
`run_focused_spec` is the hash-bound helper defined under
[Exact owner commands](#exact-owner-commands); every command waits for Lane A
to admit the exact pure-Simple CLI and core-C identities.

Wave-0 D host readiness is positive but non-promoting. The host has x86_64 and
RV64 QEMU, writable KVM, OVMF/GRUB, clang/llvm-objcopy, hosted-WM capture tools,
mtools/python, and the pinned 1,708,408-byte font with SHA-256
`2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081`.
The static-only x86 preflight
`sh scripts/check/check-simpleos-x86-64-wm-qemu-preflight.shs`, hosted-WM
wrapper `--self-test`, and RV64 wrapper `--self-test-wm-font-input` each
reported PASS. They deliberately did not run QEMU or produce acceptance
pixels. A July-27 x86 QEMU PASS under the dirty shared root is rejected: its
source hash is not bound to this feature checkout and 65 of 108 scoped source
files differ. The feature worktree still lacks the hosted binary/current
runtime evidence, x86 feature-bound evidence, RV64 ELF, admitted full CLI, and
reviewed crop pins, so all six rows retain their existing status.

| Capability | Status | Current blocker and retained-artifact state | Exact resume command | Owner / reviewer |
|---|---|---|---|---|
| Engine2D CPU/SIMD plus Vulkan selected-font draw | blocked | No current capture exists under `build/test-artifacts/03_system/app/simple_2d/feature/engine2d_font_surface_verification/`; the tracked native-lane report records hardware discovery only, not a hash-bound device PASS | `run_focused_spec test/03_system/app/simple_2d/feature/engine2d_font_surface_verification_spec.spl` after Lane A admission on a real Vulkan device | E native / `/root` |
| HTML/WebIR font and browser events | blocked | `build/test-artifacts/simple-web-font-composition/receipt.env` and `build/test-artifacts/simple-web-font-rendering-events/evidence.env` are absent; no current submitted-frame/browser-event correlation exists | export `SIMPLE_WEB_FONT_RUN_ID="font-${CHECKPOINT_SHA}-${CLI_SHA}"`, `AETHERIC_HOST_WEB_GUI_SIMPLE_BIN="$CLI"`, and an absolute retained `AETHERIC_HOST_WEB_GUI_PROOF`, then `run_focused_spec test/03_system/app/simple_web/feature/web_font_rendering_surface_spec.spl` | D surfaces / `/root` |
| GUI widget-tree font and events | blocked | `build/test-artifacts/03_system/gui/feature/gui_font_event_surface/gui_font_event.txt` is absent; source assertions and a CPU mirror are not production evidence | `run_focused_spec test/03_system/gui/feature/gui_font_event_surface_spec.spl` after Lane A admission | D surfaces / `/root` |
| Linux hosted WM live window | blocked | `build/linux-hosted-wm-font-event-current/evidence.env` and `report.md` are absent; a current X11/winit frame and reviewed glyph pin are required | `BUILD_DIR=build/linux-hosted-wm-font-event-current REPORT_PATH=build/linux-hosted-wm-font-event-current/report.md SIMPLE_BIN="$CLI" sh scripts/check/check-linux-hosted-wm-live-window-evidence.shs`, then `run_focused_spec test/03_system/gui/linux_hosted_wm_live_window_spec.spl` | D surfaces / `/root` |
| x86_64 SimpleOS QEMU WM | blocked | `build/test-simpleos-wm-fullscreen-live/evidence.env`, report, framebuffer captures, and font crop are absent. `/home/ormastes/dev/pub/simple/build/simpleos_wm_fullscreen_evidence/evidence.env` is explicitly rejected because its dirty-root source snapshot differs from this feature checkout in 65/108 scoped files | `export SIMPLE_BIN="$CLI"; run_focused_spec test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl`; the spec runs the live wrapper exactly once | D SimpleOS / `/root` |
| RV64 SimpleOS QEMU WM | blocked | the 128 MiB font disk exists, but the retained report is `status: fail`, `reason: missing-elf`; RV64 ELF, QMP scanout, input transcript, and reviewed RV64-only crop pin are absent | export the exact `BUILD_DIR`, `REPORT_PATH`, `RV64_DISPLAY_SMOKE_ELF`, `RV64_WM_FONT_DISK`, and reviewed `RV64_WM_FONT_REGION_EXPECTED_SHA256`, then `run_focused_spec test/03_system/os/wm/rv64_simpleos_wm_font_input_spec.spl`; the spec runs the live wrapper exactly once | D SimpleOS / `/root` |

No row is classified `pass`: static source, an existing Markdown file, emitted
source, CPU mirror, simulation, or a crashed command cannot prove the selected
runtime/native requirement.

## Canonical executable/manual audit

The authoritative inventory contains 32 executable specs changed or added since
`origin/main`, including current working-tree changes. Eighteen mirrored manuals
are missing, 14 are present but stale, zero are current, and zero retained owner
docgen `{out,err}` files exist. Therefore all 32 require post-admission docgen
and zero manuals have accepted current `0 stubs` evidence.

The eleven original acceptance specs are accounted for, but their mirrors are
not all current: `install_font_assets_spec.md` lacks one current scenario title,
and every assigned mirror still requires fresh zero-stub docgen evidence. The
production-surface acceptance mirrors exist for:

- `web_font_rendering_surface_spec`
- `gui_font_event_surface_spec`
- `linux_hosted_wm_live_window_spec`
- `simpleos_wm_fullscreen_spec`
- `rv64_simpleos_wm_font_input_spec`

`production_gui_font_runtime_evidence_spec.spl` is supporting backend/runtime
evidence, not an independent REQ-011 producer acceptance row; its absent manual
does not replace any canonical pair.

Eighteen changed/new specs currently lack mirrors:

- `doc/06_spec/01_unit/compiler/bootstrap/address_of_parser_spec.md`
- `doc/06_spec/01_unit/compiler/bootstrap/explicit_enum_discriminant_parser_spec.md`
- `doc/06_spec/01_unit/compiler/bootstrap/hir_lowering_error_collection_spec.md`
- `doc/06_spec/01_unit/compiler/bootstrap/legacy_core_enum_discriminant_spec.md`
- `doc/06_spec/01_unit/compiler/bootstrap/pub_mod_parser_spec.md`
- `doc/06_spec/01_unit/compiler/hir/bootstrap_impl_function_accumulation_spec.md`
- `doc/06_spec/01_unit/compiler/mir/address_of_lowering_spec.md`
- `doc/06_spec/01_unit/compiler/parser/explicit_enum_discriminant_spec.md`
- `doc/06_spec/01_unit/lib/common/text_layout/font_render_config_spec.md`
- `doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_result_spec.md`
- `doc/06_spec/01_unit/lib/skia/ot_layout_apply_spec.md`
- `doc/06_spec/01_unit/lib/skia/ot_layout_gpos_spec.md`
- `doc/06_spec/01_unit/lib/skia/ot_layout_pinned_inventory_spec.md`
- `doc/06_spec/01_unit/lib/skia/ot_parser_layout_selector_spec.md`
- `doc/06_spec/01_unit/lib/skia/ot_parser_spec.md`
- `doc/06_spec/01_unit/lib/skia/shaper_spec.md`
- `doc/06_spec/02_integration/compiler/explicit_enum_discriminant_runtime_spec.md`
- `doc/06_spec/02_integration/rendering/wm_nested_content_frame_spec.md`

Fourteen existing mirrors are stale because their executable sources changed in this
all-items worktree and no current pure-Simple docgen result exists:

- `install_font_assets_spec.md`
- `font_asset_manifest_spec.md`
- `gui_entry_desktop_production_render_contract_spec.md`
- `simpleos_font_asset_staging_spec.md`
- `legacy_web_gui_wm_font_route_spec.md`
- `shared_font_manifest_spec.md`
- `shared_font_shaping_acceptance_spec.md`
- `shared_font_surfaces_spec.md`
- `web_font_rendering_surface_spec.md`
- `gui_font_event_surface_spec.md`
- `linux_hosted_wm_live_window_spec.md`
- `simpleos_wm_fullscreen_spec.md`
- `rv64_simpleos_wm_font_input_spec.md`
- `shared_multilingual_gpu_fonts_perf_spec.md`

The aggregate `shared_font_surfaces_spec.spl` now uses the frozen
`step("Prepare one shared font batch for 2D and 3D")`; its mirror is stale until
canonical regeneration. The perf owner likewise changed to the frozen
`step("Measure warm font rendering and resource bounds")`; its mirror remains
stale until canonical regeneration. Hand edits cannot substitute for docgen.

Static scans found no `pass_todo`, `expect(true).to_equal(true)`,
`pass_do_nothing`, or `pass_dn` in the aggregate acceptance specs.
`find doc/06_spec -name '*_spec.spl' -print` returned no paths. These are static
checks only.

The current HIP-to-ROCm batch, degenerate-Web fail-closed, nested WM IMAGE, and
shared nested-frame collector changes remain unverified implementation evidence.
The collector's source spec covers a valid reachable collection plus
fail-closed stale, duplicate, and orphan rejection; its mirror is missing and
the behavioral cases have not run on an admitted CLI.

### Lane F static source/manual-quality audit

The retained pre-REQ-016 audit found no `pass_todo`, tautological
`expect(true).to_equal(true)`, `to_raise`, or empty scenario body. Its
scenario/expect counts predate the four REQ-016 specs and the changed
selected-Devanagari policy spec, so they are not current 32-source evidence;
lane F must audit all 32 sources after an admitted runtime is available.
The four `pass_do_nothing` calls in
`wm_nested_content_frame_spec.spl` are explicitly justified no-op methods on
the pixel-only fixture (`draw_text`, `draw_char_8x16`, `present`, and
`present_rect`), not scenario passes.

All eight frozen manual steps remain present in their owning acceptance sources:
manifest load, exact-face shaping, shared 2D/3D batch preparation, portable
emission, native submission/readback, legacy Web/GUI/WM Draw IR, SimpleOS pixel
capture, and warm rendering/resource measurement.

Lane C resolved all 19 previously reported noncanonical matchers. It also
repaired two short-expression parse defects: the split GSUB context-rule
inequality in `ot_layout_apply.spl`, and wrapped boolean continuations in the
canonical layout shaper. These are source-present but runtime-unverified.

The selected-memory binder now accepts parsed bytes only when the fallback
primary has no live handle, its path is an exact selected-registry path, and
the registry identity starts with the parsed blob's exact SHA-256 plus its
axis identity. Arbitrary paths and selected-path/mismatched-byte combinations
remain unbound. This hardening and its direct regression are also
source-present but runtime-unverified.

The pinned GSUB/GPOS support map is deliberately narrow:

The full REQ-016 audit rejects the former pinned-map completion claim. The
merged baseline implements GSUB 1–8 and GPOS 1–9 with split subtable owners,
fixes the context-format-3 input increment, admits all defined LookupFlag/GDEF
filters, evaluates supported FeatureVariations, and decodes
Device/VariationIndex plus anchor formats 2/3. ExtensionSubst rejects a nested
type-7 target, as required by the OpenType extension contract. The selected
high-level complex-script boundary remains fail-closed outside explicitly
supported preprocessing; the complete lower-level GSUB/GPOS executor does not
turn that boundary into a claim of general Indic preprocessing. Source review
then closed the production gaps: one shared GPOS data context/budget reaches
validation, nested dispatch, and application; PairPos resolves Device offsets
from its owning subtable; packed Device pixels remain post-scale while
VariationIndex stays in design units; public shaping forwards normalized
coordinates and LangSys; GSUB preserves device fields; and contextual edits
compose old-to-new position maps. Focused source regressions exist, but no
full-layout claim is valid until they execute on the admitted runtime.

Each row selects both GSUB and GPOS plans. Acceptance remains limited to the
exact pinned Hindi, Arabic, and Urdu witnesses and the recorded simple-script
identity cases; it does not claim general GSUB/GPOS, BiDi, mark, language, or
arbitrary-font support.

Of the 14 stale manuals, six still contain every current scenario title and
eight omit at least one current title. `font_asset_manifest_spec.md` and
`gui_entry_desktop_production_render_contract_spec.md` explicitly identify
themselves as manually synchronized/docgen-pending. Hand synchronization is not
generated evidence. The nine absent mirrors and all 14 stale mirrors therefore
remain rejected until deterministic docgen succeeds with `0 stubs`.

## Exact owner commands

The authoritative docgen scope is the 32 changed/new specs classified above.
Each source owner retains stdout and stderr separately under
`docgen/preflight/<path-derived-basename>.{out,err}`; lane F audits all 32.

All retained paths are below
`build/test-artifacts/shared_multilingual_gpu_fonts/`. For each assigned source
path, the owner runs:

```bash
"$CLI" spipe-docgen <assigned-spec> --output doc/06_spec --no-index \
  > "build/test-artifacts/shared_multilingual_gpu_fonts/docgen/lane-<owner>/<basename>.out" \
  2> "build/test-artifacts/shared_multilingual_gpu_fonts/docgen/lane-<owner>/<basename>.err"
```

Lane A must first produce and admit one pure-Simple full CLI in a fresh bounded
session, using the retained resume contract:

```bash
timeout -k 30s 3600s env SIMPLE_NO_STUB_FALLBACK=1 \
  scripts/bootstrap/bootstrap-from-scratch.sh \
  --backend=cranelift \
  --output=build/test-artifacts/shared_multilingual_gpu_fonts/bootstrap/full-bootstrap \
  --full-bootstrap --full-cli --no-mcp --jobs=4
```

Only an exit-0 wrapper result may publish the candidate. Run
`scripts/check/check-bootstrap-essential-tools-smoke.shs` against that exact
candidate, then retain its absolute path and SHA-256 plus the core-C directory
and `libsimple_runtime.a` SHA-256. A Rust seed or exit `2`, `124`, `132`, or
`139` is a blocker.

After lane A publishes those immutable values, set:

```bash
CLI=/absolute/path/to/deployed/pure-simple
CLI_SHA=<deployed-cli-sha256>
CORE_C_DIR=/absolute/path/to/deployed/core-c
CORE_C_SHA=<deployed-libsimple_runtime.a-sha256>
CHECKPOINT_SHA=$(git rev-parse HEAD)
```

Lane A first runs the shared essential-tools admission gate against that exact
binary and retains both streams:

```bash
ESSENTIAL_ROOT=build/test-artifacts/shared_multilingual_gpu_fonts/essential-tools
mkdir -p "$ESSENTIAL_ROOT"
CLI_ACTUAL_SHA=$(sha256sum "$CLI" | awk '{print $1}')
[ "$CLI_ACTUAL_SHA" = "$CLI_SHA" ]
SIMPLE_BINARY="$CLI" sh scripts/check/check-bootstrap-essential-tools-smoke.shs \
  >"$ESSENTIAL_ROOT/smoke.out" 2>"$ESSENTIAL_ROOT/smoke.err"
```

The command must exit zero and its retained stdout must contain
`essential_test_runner_smoke=true`, `essential_lint_smoke=true`,
`essential_duplicate_checker_smoke=true`, and
`bootstrap_essential_tools_smoke=true`. A wrapper, Rust seed, stale hash, or
missing marker is not admission.

The essential-tools gate already executes the clean lint and duplicate-check
probes and validates their exact success markers. Do not run those unchanged
commands a second time; the retained gate streams are the one admission record.

Lane A calibrates the runner once globally before any focused result:

```bash
CAL_ROOT=build/test-artifacts/shared_multilingual_gpu_fonts/runner-calibration
mkdir -p "$CAL_ROOT"
CORE_C_ACTUAL_SHA=$(sha256sum "$CORE_C_DIR/libsimple_runtime.a" | awk '{print $1}')
[ "$CORE_C_ACTUAL_SHA" = "$CORE_C_SHA" ]
{
  printf 'checkpoint_sha=%s\n' "$CHECKPOINT_SHA"
  printf 'cli=%s\ncli_sha256=%s\n' "$CLI" "$CLI_SHA"
  printf 'core_c_dir=%s\ncore_c_sha256=%s\n' "$CORE_C_DIR" "$CORE_C_SHA"
} >"$CAL_ROOT/identity.env"

record_command() {
  output=$1
  shift
  {
    printf 'command'
    printf ' %q' "$@"
    printf '\n'
  } >"$output"
}

record_command "$CAL_ROOT/fail.command" \
  "$CLI" run src/app/test/font_evidence_runner.spl -- \
  "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA" \
  scripts/check/fixtures/font_evidence_runner_fail_spec.spl
if "$CLI" run src/app/test/font_evidence_runner.spl -- \
    "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA" \
    scripts/check/fixtures/font_evidence_runner_fail_spec.spl \
    >"$CAL_ROOT/fail.out" 2>"$CAL_ROOT/fail.err"; then
  fail_rc=0
else
  fail_rc=$?
fi
printf '%s\n' "$fail_rc" >"$CAL_ROOT/fail.exit"

record_command "$CAL_ROOT/empty.command" \
  "$CLI" run src/app/test/font_evidence_runner.spl -- \
  "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA" \
  scripts/check/fixtures/font_evidence_runner_empty_spec.spl
if "$CLI" run src/app/test/font_evidence_runner.spl -- \
    "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA" \
    scripts/check/fixtures/font_evidence_runner_empty_spec.spl \
    >"$CAL_ROOT/empty.out" 2>"$CAL_ROOT/empty.err"; then
  empty_rc=0
else
  empty_rc=$?
fi
printf '%s\n' "$empty_rc" >"$CAL_ROOT/empty.exit"

[ "$fail_rc" -eq 1 ]
[ "$empty_rc" -eq 1 ]
grep -Fq 'test-runner: spec failed' "$CAL_ROOT/fail.out"
grep -Fq 'test-runner: no examples executed' "$CAL_ROOT/empty.out"
```

The first command must exit 1 with `test-runner: spec failed`; the second must
exit 1 with `test-runner: no examples executed`. Retain both logs and the exact
command lines under
`build/test-artifacts/shared_multilingual_gpu_fonts/runner-calibration/`.
Lanes B–E reference that one immutable calibration set; they do not rerun it.

Every focused spec uses the same hash-bound runner:
`src/app/test/font_evidence_runner.spl` forwards only the ten reviewed native
variables: `SIMPLE_BIN`, `SIMPLE_BINARY`, `SIMPLE_WEB_FONT_RUN_ID`,
`AETHERIC_HOST_WEB_GUI_SIMPLE_BIN`, `AETHERIC_HOST_WEB_GUI_PROOF`, `BUILD_DIR`,
`REPORT_PATH`, `RV64_DISPLAY_SMOKE_ELF`, `RV64_WM_FONT_DISK`, and
`RV64_WM_FONT_REGION_EXPECTED_SHA256`. It does not forward arbitrary ambient
host state.

```bash
FOCUSED_ROOT=build/test-artifacts/shared_multilingual_gpu_fonts/focused
FOCUSED_ATTEMPT=${FOCUSED_ATTEMPT:-1}
case "$FOCUSED_ATTEMPT" in
  1|2|3) ;;
  *) echo "invalid focused attempt: $FOCUSED_ATTEMPT" >&2; exit 2 ;;
esac

run_focused_spec() {
  spec=$1
  name=${spec#test/}
  name=${name//\//_}
  root="$FOCUSED_ROOT/attempt-$FOCUSED_ATTEMPT"
  mkdir -p "$root"
  [ ! -e "$root/$name.command" ] || {
    echo "refusing duplicate focused execution: $spec" >&2
    return 125
  }
  {
    printf 'checkpoint_sha=%s\nattempt=%s\nspec=%s\n' \
      "$CHECKPOINT_SHA" "$FOCUSED_ATTEMPT" "$spec"
    printf 'SIMPLE_BIN=%s\nSIMPLE_WEB_FONT_RUN_ID=%s\n' \
      "${SIMPLE_BIN:-}" "${SIMPLE_WEB_FONT_RUN_ID:-}"
    printf 'SIMPLE_BINARY=%s\nAETHERIC_HOST_WEB_GUI_SIMPLE_BIN=%s\n' \
      "${SIMPLE_BINARY:-}" "${AETHERIC_HOST_WEB_GUI_SIMPLE_BIN:-}"
    printf 'AETHERIC_HOST_WEB_GUI_PROOF=%s\n' \
      "${AETHERIC_HOST_WEB_GUI_PROOF:-}"
    printf 'BUILD_DIR=%s\nREPORT_PATH=%s\n' \
      "${BUILD_DIR:-}" "${REPORT_PATH:-}"
    printf 'RV64_DISPLAY_SMOKE_ELF=%s\nRV64_WM_FONT_DISK=%s\n' \
      "${RV64_DISPLAY_SMOKE_ELF:-}" "${RV64_WM_FONT_DISK:-}"
    printf 'RV64_WM_FONT_REGION_EXPECTED_SHA256=%s\n' \
      "${RV64_WM_FONT_REGION_EXPECTED_SHA256:-}"
    printf 'command'
    printf ' %q' "$CLI" run src/app/test/font_evidence_runner.spl -- \
      "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA" "$spec"
    printf '\n'
  } >"$root/$name.command"
  if "$CLI" run src/app/test/font_evidence_runner.spl -- \
      "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA" "$spec" \
      >"$root/$name.out" 2>"$root/$name.err"; then
    rc=0
  else
    rc=$?
  fi
  printf '%s\n' "$rc" >"$root/$name.exit"
  [ "$rc" -eq 0 ]
  grep -Fq 'test-runner: native result wrapper complete' "$root/$name.out"
}
```

Attempt 1 is the only initial execution. Attempts 2 and 3 are reserved for an
owner repair that changes the failing source; an unchanged green or unchanged
failure is never rerun. The command, both streams, and exit code remain
immutable under the attempt directory.

Lane B executes once each:

```bash
run_focused_spec test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl
run_focused_spec test/01_unit/app/release/install_font_assets_spec.spl
run_focused_spec test/01_unit/app/release/release_archive_layout_spec.spl
run_focused_spec test/01_unit/lib/common/encoding/font_asset_manifest_spec.spl
run_focused_spec test/01_unit/os/port/simpleos_font_bundle_spec.spl
run_focused_spec test/02_integration/os/port/simpleos_font_asset_staging_spec.spl
```

Lane C executes the aggregate and integrated shaping gates once each:

```bash
run_focused_spec test/03_system/app/simple_2d/feature/shared_font_shaping_acceptance_spec.spl
run_focused_spec test/03_system/app/simple_2d/feature/shared_font_surfaces_spec.spl
run_focused_spec test/01_unit/lib/skia/ot_layout_apply_spec.spl
run_focused_spec test/01_unit/lib/skia/ot_layout_gpos_spec.spl
run_focused_spec test/01_unit/lib/skia/ot_layout_pinned_inventory_spec.spl
run_focused_spec test/01_unit/lib/skia/ot_parser_layout_selector_spec.spl
run_focused_spec test/01_unit/lib/skia/ot_parser_spec.spl
run_focused_spec test/01_unit/lib/skia/shaper_spec.spl
run_focused_spec test/01_unit/lib/skia/selected_devanagari_spec.spl
run_focused_spec test/01_unit/lib/skia/selected_arabic_spec.spl
run_focused_spec test/01_unit/lib/common/text_layout/font_renderer_spec.spl
run_focused_spec test/01_unit/lib/common/text_layout/font_render_config_spec.spl
run_focused_spec test/01_unit/lib/gpu/engine3d/font_compat_spec.spl
```

Lane D first executes its shared Engine2D prerequisite once:

```bash
run_focused_spec test/03_system/app/simple_2d/feature/engine2d_font_surface_verification_spec.spl
```

After that passes, Lane D executes the independent producer rows once each.
The Web row receives a nonempty immutable run ID. The x86 and RV64 specs run
their live wrappers internally, so no separate live-wrapper command precedes
them. Export the wrapper inputs so those child processes use the admitted CLI
and exact retained artifacts:

```bash
run_focused_spec test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_result_spec.spl
run_focused_spec test/01_unit/os/gui_entry_desktop_production_render_contract_spec.spl
run_focused_spec test/02_integration/rendering/wm_nested_content_frame_spec.spl
run_focused_spec test/03_system/app/simple_2d/feature/legacy_web_gui_wm_font_route_spec.spl
export SIMPLE_WEB_FONT_RUN_ID="font-${CHECKPOINT_SHA}-${CLI_SHA}"
export AETHERIC_HOST_WEB_GUI_SIMPLE_BIN="$CLI"
export AETHERIC_HOST_WEB_GUI_PROOF=/absolute/path/to/retained/aetheric-host-web-gui.env
run_focused_spec test/03_system/app/simple_web/feature/web_font_rendering_surface_spec.spl
run_focused_spec test/03_system/gui/feature/gui_font_event_surface_spec.spl
# Generate the hosted live bundle once with the capability-row command above;
# this focused spec consumes and validates that retained bundle.
run_focused_spec test/03_system/gui/linux_hosted_wm_live_window_spec.spl
export SIMPLE_BIN="$CLI"
run_focused_spec test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl
export BUILD_DIR=build/test-artifacts/shared_multilingual_gpu_fonts/req011/rv64-live
export REPORT_PATH="$BUILD_DIR/report.md"
export RV64_DISPLAY_SMOKE_ELF=build/os/simpleos_riscv64_display_smoke.elf
export RV64_WM_FONT_DISK=build/os/fat32-riscv64-desktop.img
export RV64_WM_FONT_REGION_EXPECTED_SHA256="<reviewed-rv64-crop-sha256>"
run_focused_spec test/03_system/os/wm/rv64_simpleos_wm_font_input_spec.spl
```

Lane E executes once each on a real graphics device:

```bash
run_focused_spec test/03_system/app/simple_2d/feature/gpu_font_emission_spec.spl
run_focused_spec test/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.spl
run_focused_spec test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl
run_focused_spec test/05_perf/graphics_2d/shared_multilingual_gpu_fonts_perf_spec.spl
```

The B–E command graph contains 37 unique focused executions: 6 in B, 17 in C,
10 in D including its Engine2D prerequisite, and 4 in E. No path appears in
more than one group.

Each of the 32 docgen commands must exit zero and report the affected spec
complete with `0 stubs`. The owner retains both output streams; lane F reviews
the generated operator flow.

## Final gates owned by `/root`

```bash
find doc/06_spec -name '*_spec.spl' -print
sh scripts/audit/direct-env-runtime-guard.shs --working
sh scripts/audit/direct-env-runtime-guard.shs --staged
sh scripts/audit/numbered-artifact-guard.shs --working
sh scripts/audit/numbered-artifact-guard.shs --staged
git diff --check
```

The first command must print nothing. Final verification remains `STATUS: FAIL`
until every blocked row has authoritative evidence; unavailable hardware stays
a blocker rather than a synthetic or static PASS.
