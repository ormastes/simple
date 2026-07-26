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
| REQ-001 | active | B manifest/distribution | `shared_font_manifest_spec.spl` and mirror cover pins, order, totals, boundary | admitted CLI; run B command set below | `/root` |
| REQ-002 | active | B manifest/distribution | same pair covers decimal contribution, alias policy, deterministic regeneration | admitted CLI; run B command set | `/root` |
| REQ-003 | active | B+C manifest/shaping | manifest and shaping acceptance pairs cover sparse states and fail-closed cells | admitted CLI; run B and C command sets | `/root` |
| REQ-004 | active | B manifest/distribution | manifest, asset-manifest, installer, archive, SimpleOS bundle/staging specs exist; mirrors exist for the acceptance pairs | admitted CLI; run B command set and zero-stub docgen | `/root` |
| REQ-005 | active | B manifest/distribution | manifest and SimpleOS bundle specs cover the pinned candidate catalog and unchanged bytes | admitted CLI; run B command set | `/root` |
| REQ-006 | active | C+D shaping/surfaces | `shared_font_surfaces_spec.spl` and legacy Web/GUI/WM route pair cover the shared owner/material seam | admitted CLI; run aggregate and D command sets | `/root` |
| REQ-007 | active | C shaping/material | shaping acceptance plus selected Arabic/Devanagari and six integrated GSUB/GPOS unit specs exist | admitted CLI; run C command set; generate six missing unit mirrors | `/root` |
| REQ-008 | active | B+C manifest/shaping | manifest and parser/loader specs cover `glyf`, default instance, bitmap, and rejection policy | admitted CLI; run B/C command sets | `/root` |
| REQ-009 | active | C+E material/native | renderer, aggregate surface, emission, backend and perf specs contain cache identity/lifecycle oracles | admitted CLI and native record; run C/E sets | `/root` |
| REQ-010 | active | E native/emission | GPU emission and CUDA handoff executable/manual pairs cover source/artifact contracts; emission is not execution | admitted CLI; run E source commands; retained native artifact required for promotion | `/root` |
| REQ-011 | active | D+E surfaces/native | aggregate surfaces/route plus canonical Web, GUI, hosted WM, SimpleOS and RV64 pairs exist; working changes add fail-closed degenerate Web status, ancestor-clipped nested IMAGE projection, and shared nested-collector cases for valid collection plus stale/duplicate/orphan rejection | changes are source-present but runtime-unverified; admitted CLI, hosted frame and QEMU pixels required; run D/E sets | `/root` |
| REQ-012 | blocked | E native 2D/3D/perf | native readback spec contains HUD/world, handles, submit, fence, depth/transform and readback gates | admitted CLI plus real graphics device; run E native command | `/root` |
| REQ-013 | blocked | E native 2D/3D/perf | native readback spec rejects unavailable and forged promotion | one real backend must pass both 2D and 3D through E native command | `/root` |
| REQ-014 | blocked | A–E generation / F audit | among 32 changed/new specs, 18 mirrors are missing, 14 are stale, zero are current, and no retained log proves `0 stubs` | admitted CLI; run all 32 docgen commands below; review manuals | `/root` |
| REQ-015 | active | C shaping/material/config | aggregate surfaces and focused config specs cover identity, policies, target order and pre-mutation rejection; working changes canonicalize HIP to ROCm on the prepared batch | batch change is unverified; admitted CLI required; run aggregate/C commands | `/root` |
| NFR-001 | active | B manifest/distribution | manifest and SimpleOS bundle source gates cover immutable hashes, deterministic generation and corruption rejection | admitted CLI; run B command set | `/root` |
| NFR-002 | blocked | E native/perf | native readback and perf specs define exact packed-ARGB comparator and provenance fields | admitted CLI plus real device; run E native/perf commands | `/root` |
| NFR-003 | active | B manifest/distribution | manifest/bundle gates encode the 80 MiB and SimpleOS projection limits | admitted CLI; run B command set | `/root` |
| NFR-004 | blocked | E native/perf | performance spec and manual define warm hit and 1080p/4K p95 thresholds | real device must create a valid `build/shared_multilingual_gpu_fonts_perf/evidence.env` | `/root` |
| NFR-005 | blocked | E native/perf | performance spec defines equal-semantics 4,096-glyph CPU/GPU comparison | real promoted backend must prove at least 1.25x using E perf command | `/root` |
| NFR-006 | blocked | E native/perf | performance spec defines unchanged upload, RSS delta and GPU high-water checks | real device plus isolated RSS probe; run E perf command | `/root` |
| NFR-007 | blocked | E native/perf | native/perf specs define corrupt/device-loss fallback and unchanged identity/p95 checks | retained native fault-injection execution required | `/root` |
| NFR-008 | blocked | E native/perf | native/perf records require shaping through readback/resource stages | retained nonzero handles, fence and device-origin readback required | `/root` |

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
CLI=/absolute/path/to/admitted/pure-simple
CLI_SHA=<published-cli-sha256>
CORE_C_DIR=/absolute/path/to/admitted/core-c
CORE_C_SHA=<published-libsimple_runtime.a-sha256>
```

Lane A calibrates the runner once globally before any focused result:

```bash
CAL_ROOT=build/test-artifacts/shared_multilingual_gpu_fonts/runner-calibration
mkdir -p "$CAL_ROOT"
"$CLI" run src/app/test/font_evidence_runner.spl -- "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA" scripts/check/fixtures/font_evidence_runner_fail_spec.spl >"$CAL_ROOT/fail.out" 2>"$CAL_ROOT/fail.err"
printf '%s\n' "$?" >"$CAL_ROOT/fail.exit"
"$CLI" run src/app/test/font_evidence_runner.spl -- "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA" scripts/check/fixtures/font_evidence_runner_empty_spec.spl >"$CAL_ROOT/empty.out" 2>"$CAL_ROOT/empty.err"
printf '%s\n' "$?" >"$CAL_ROOT/empty.exit"
```

The first command must exit 1 with `test-runner: spec failed`; the second must
exit 1 with `test-runner: no examples executed`. Retain both logs and the exact
command lines under
`build/test-artifacts/shared_multilingual_gpu_fonts/runner-calibration/`.
Lanes B–E reference that one immutable calibration set; they do not rerun it.

Every focused spec uses the same hash-bound runner:

```bash
run_focused_spec() {
  "$CLI" run src/app/test/font_evidence_runner.spl -- \
    "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA" "$1"
}
```

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

Lane D executes its independent producer rows once each:

```bash
run_focused_spec test/03_system/app/simple_web/feature/web_font_rendering_surface_spec.spl
run_focused_spec test/03_system/gui/feature/gui_font_event_surface_spec.spl
run_focused_spec test/03_system/gui/linux_hosted_wm_live_window_spec.spl
run_focused_spec test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl
run_focused_spec test/03_system/os/wm/rv64_simpleos_wm_font_input_spec.spl
```

Lane E executes once each on a real graphics device:

```bash
run_focused_spec test/03_system/app/simple_2d/feature/gpu_font_emission_spec.spl
run_focused_spec test/03_system/app/simple_2d/feature/cuda_generated_font_handoff_spec.spl
run_focused_spec test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl
run_focused_spec test/05_perf/graphics_2d/shared_multilingual_gpu_fonts_perf_spec.spl
```

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
