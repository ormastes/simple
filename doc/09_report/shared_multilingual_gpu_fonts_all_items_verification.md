# Shared Multilingual GPU Fonts — All-Items Verification

Date: 2026-07-26
Authority: selected requirements and NFRs in
`doc/02_requirements/{feature,nfr}/shared_multilingual_gpu_fonts.md`
Final done-mark owner: highest-capability `/root`

## Result

`STATUS: FAIL`

This is the current all-lane audit, not a runtime or native PASS.
Compiler-enablement work is not a shared-font acceptance criterion and cannot
promote a font row. The branch nevertheless retains the minimal HirBlock,
lowering-error collector, native-arena, and direct-entry repairs needed to
produce the pure-Simple prerequisite.

### Current bootstrap blocker

The current synced checkpoint is
`616454901c666f87e2cb7d70719d8d076ec81a1d`. The earlier pushed checkpoint
`2eb2bbf93f10` is historical. Completion still requires the final
fetch/rebase/file-count gate against the then-current `origin/main`.
At the earlier source checkpoint `deb90cd8a9c`, both direct-runtime guards,
both numbered-artifact guards, `git diff --check`, and the
zero-executable-specs-under-`doc/06_spec` layout gate passed. Those retained
static results do not prove the current checkout, runtime behavior, or a
native row.

No Stage 4 CLI/core-C identity was published and no global runner calibration
ran. The three-check cap is reached; no further retry is permitted this
session. A fresh session must verify the integrated accumulator and typed-index
collector before any downstream evidence can be accepted.

A separate read-only monitor observed the external compiler workspace produce
compiler-only Stage3 SHA-256
`704f67af420bd8788dda809b46112d0a9a76cec64601ebfe2a6958a894aa380f`,
then fail Stage4 at `src/std/nogc_sync_mut/env/variables.spl:364`. `src/std`
is the tracked `src/lib` symlink, so the canonical source path is
`src/lib/nogc_sync_mut/env/variables.spl`. A clean current checkout already
uses the safe Option form following the non-nil guard; this identifies the
external dirty checkout as stale rather than a new parser or font-source
defect. One fresh full-CLI build from a clean current compiler checkout still
must be admitted before focused runtime evidence can begin; no full CLI was
produced. The retained Stage4 log is
`/home/ormastes/dev/pub/simple-bootstrap/build/mini_builds/bootstrap-memory-lexer-fix-stage4-cycle2.log`
(SHA-256 `1a6e74e630d3341898cecfe9e785f9802527b96ae2372583531c8f52d17f09a9`).
That clean-current full-CLI admission is the exact prerequisite before focused
font test/docgen/native verification can resume.

One isolated clean-current attempt was made only because this admission is
essential. Rust seed
`/home/ormastes/dev/pub/simple/src/compiler_rust/target/bootstrap/simple` ran
against clean HEAD `16ebfdb6410` in `/tmp/simple-clean-cli-20260726`, but was
terminated with SIGTERM after 2m15s before compilation/object output. No
candidate CLI emerged. Its final meaningful log line was the pre-compilation
memory guard warning that `SIMPLE_LIB=src` contains 600+ `.spl` files; retained
log: `/tmp/simple-clean-cli-20260726/build/mini_builds/full_cli_seed_cycle1.log`.
This is a separate compiler/runtime build-system blocker. The font lane must
not restart it; its owner must resolve that admission path and deliver one
full CLI before the queued verification can resume.

A final P0 admission lane in `/tmp/simple-pure-cli-font-20260727` at
`1d75d521b775` spent the three permitted incremental cycles with retained
pure-Simple Stage3 compiler SHA-256
`704f67af420bd8788dda809b46112d0a9a76cec64601ebfe2a6958a894aa380f`.
Cycle 3 stopped in
`src/std/nogc_sync_mut/compression/gzip/lz77.spl`: line 104 binds the reserved
keyword in `val match = ...`, and line 105 uses it in
`val distance = match[0]`. The retained parser reads that use as a `match`
expression and first reports `expected :, got Newline`; the line-106
`length` diagnostics are recovery cascades, and `length` is not reserved.
The retained and clean-current token tables are byte-identical at SHA-256
`cfea0c9e2063eae474913ee9cbfd585d29dfd50323c24c375d23656b884119da`,
and all three logs retain the same parse ordering, with cycle 3 reaching 801
of 1,309 unique physical sources. No candidate ELF and no native-cache
object/file were produced. The retained logs and SHA-256 values
are `build/mini_builds/full_cli_incremental_cycle1.log`
(`82a5b6bf68efc867e7e8cf4107ebe29f14590ec422e7646a87eac10f1fdad389`),
`full_cli_incremental_cycle2.log`
(`c1e4e61d1cf919478793017859c09cc021938863a651ab198e48f37759f1f8dd`),
and `full_cli_incremental_cycle3.log`
(`4bab47a3a0ff2164508db9ada5433cfbe85b8fdeb100756328b8869450e39dc7`).
The historical continuation at that checkpoint called for a canonicalized
closure preflight and an isolated compatibility bridge. That instruction is
superseded by the current fresh-Stage2 plan below. Only the genuine
current-language `class` local corrections in
`src/lib/skia/feature/shaper/ot_layout_gpos.spl:123,602` belong in the font
branch; the 13-file bridge overlay remains isolated, uncommitted, and
unmerged. The three-cycle cap is reached; this blocker does not promote any
runtime-dependent font row.

A fresh compatibility-bridge continuation then ran in detached worktree
`/tmp/simple-cli-bridge-20260727-2` at feature checkpoint `397afaaee3bb`.
The bridge remained isolated and uncommitted. Its three bounded cycles cleared
the reserved-keyword and multiline-boolean parser blockers and the first
`FileTreeState` HIR type gap, but still produced no ELF and zero cached object
files. Cycle 3 raised the per-file limit from 60 to 180 seconds and stopped on
two terminal blockers: the 9,716-line
`src/app/office/sheets/formula.spl` still exceeded 180 seconds, and
`src/lib/editor/70.backend/gui_backend.spl` reached the next missing direct
type resolution (`SettingsViewState.categories` is lowered as `ANY` in
`gui_render_settings_html`). The three retained log SHA-256 values are
`1a4c04ee995bb80ac55e3650e7088e773326f8b16bc25d9c8952d016b3886def`,
`43e9dff528a8ce0f33746be503368bcbd416c6eb22c85c43867bcc06d89adc7a`,
and `09e3e54a99ab7d76681ca2a27cd285b8ebb71932b27fed65a15ee133c0508c12`.
No essential-tools smoke ran because no candidate existed. The session cap was
reached; its former resume instruction is historical and superseded by the
current fresh-Stage2 plan.

The next isolated continuation used detached worktree
`/tmp/simple-cli-bridge-20260727-3` at `fefcfe011fc0053d0ab3e01a13005bb841db5023`
and the same retained Stage3 compiler. The bridge avoided eager Office/IDE
entry closure, added the proven GUI type imports, and selected the complete
Rust runtime archives. Cycle 1 retained 1,417 objects before a link-only
failure exposed the incomplete default runtime bundle and missing GSUB
`_sub_end`; cycle 2 cleared those blockers and stopped on one canonical CSS
import plus the duplicate `ant-trace`/`ant_trace` module; cycle 3 cleared the
full import/collision preflight and parsed 806 of 1,190 unique files before the
retained parser rejected `loop.induction_var` in
`auto_vectorize_analysis.spl`. Log SHA-256 prefixes are `b5db2444`,
`567d1e0d`, and `7732687e`. No ELF or smoke result exists. The genuine bounded
GSUB helper is integrated; all remaining compatibility edits stay isolated.
The three-cycle cap was reached. Its retained-cache resume instruction is
historical and superseded by the current fresh-Stage2 plan.

A later fresh three-cycle bridge window reused the same Stage3 SHA-256
`704f67af420bd8788dda809b46112d0a9a76cec64601ebfe2a6958a894aa380f`
and all 1,417 retained objects. Cycle 1 rejected `pub mod` at
`src/compiler/10.frontend/core/__init__.spl:111`; cycle 2 cleared that bridge
syntax and then rejected five address-of forms, first
`src/os/userlib/device.spl:26`; cycle 3 cleared those exact closure forms and
stopped at the sparse ABI enum discriminants beginning with
`src/os/kernel/types/syscall_types.spl:8`. The retained log SHA-256 values are
`641d8754567044305afeb9abe612bd86b1fbbcbafffc40d6f57a3c168ac34fce`,
`6559f179b3058111fc72718864d1dc9ee642cf401f93a1f684781b05aacdc48d`,
and `f8bb267073a05f345319d36c1622d5477751be45249ff0d6b1063f3664fc8a32`.
No ELF, Stage5, or essential-tools smoke exists. The bridge remains isolated;
the former sparse-ABI continuation is historical and superseded by the current
fresh-Stage2 plan.

Fresh admission lane `/tmp/simple-cli-admission-20260727-4` then preserved all
106 sparse ABI values through exhaustive enum-to-number converters and reused
the 1,417-object cache. Cycle 1 cleared three tuple-destructuring loops
(`build/mini_builds/full_cli_admission_cycle1.log`, SHA-256
`769acbbb1a10cc1cb825f1704a7e563118e42a3725290fcaff5a508fc6e4a7ae`);
cycles 2 and 3 both parsed the 1,190-file closure and lowered all 28 functions
in `src/lib/gc_async_mut/gpu/engine2d/color.spl`, then the retained pure-Simple
Stage3 trapped on `field access on nil receiver` and exited 132. Their log
paths are `build/mini_builds/full_cli_admission_cycle2.log` and
`build/mini_builds/full_cli_admission_cycle3.log`; their SHA-256 values are
`024699a05dc5ebcd6452f0539b1f361294679b9a7b3039a7f0a8eee8df5f05ad`
and `c63e11b391f2254971bb767a12f500d2107635ad230e8774528bb138874b68a3`.
The repeated result ended the window at its three-cycle cap. No Stage4 ELF,
Stage5, or smoke result exists; the compatibility bridge remains isolated.

The earlier read-only inference that localized the failure to
`HirLowering.lower_module`'s final diagnostic `eprint` is retained only as
superseded history. The authoritative kernel trap records instruction pointer
`0x559924`. In the retained Stage3 binary this is the `ud2` immediately after
`MethodResolver.resolve_expr` masks its incoming `expr` argument and detects
nil or a low-tag-only value. The normal `rdi=self`, `rsi=expr` register setup
is intact, so the evidence points to an upstream HIR value-representation
error rather than a SysV argument-register error.

`color.spl` still completed all 28 HIR functions. Its first resolution-order
function, `color_black`, ends in `rgb(0, 0, 0)`, providing the concrete Call
tail that reaches the bad boundary. `HirBlock` is desugared as `has: bool`
plus a mandatory `HirExpr`, but ten sites retained the older Option contract:
five consumers matched or unwrapped `block.value` as `Option`, and five
synthetic constructors supplied `Some(...)` or bare `nil`. In particular,
`resolve_block` could extract the Call tail as though it were an Option payload
and pass the resulting nil or low-tag-only value into `resolve_expr`.

Current source integrates the narrow invariant repair: all five consumers gate
on `block.has`; all five constructors provide explicit `has` plus a typed tail
or `NilLit` sentinel; and lowering-error collection uses an indexed loop with
an explicit `LoweringError` binding. Focused regression sources cover the
Call-tail/empty-tail resolution boundary and the constructor/consumer
invariant. Those fixes remain execution-unverified: this correction ran no
test or build, did not rebuild Stage3/Stage4, and did not retry admission. No
Stage4 ELF, Stage5, or essential-tools smoke exists, so the pure-Simple CLI
gate remains blocking and the overall result remains `STATUS: FAIL`.

Independent static review accepted the shaping/material and surface/native
spec stacks after requiring a nonempty selected font identity, explicit
Arabic/Urdu/Hindi direction, and exact Web advance-width propagation through
the proof validator. It rejected the first manifest/distribution rewrite for
private production imports and added heavyweight fixed-`/tmp` unit staging.
The current replacement uses the existing public font-registry APIs, validates
the real immutable bundle root, and rejects an intermediate `assets` symlink
before walking or hashing bundle files. It adds no duplicate facade or staged
font copy. These source-only results remain blocked on the admitted runtime and
do not promote a requirement or NFR.

### Deployed-runtime boundary

- Retain the deployed pure-Simple runtime path and identity used for each
  focused command.
- Reject Rust-seed execution, zero-example results, and unauthenticated
  summaries.
- Do not introduce compiler, interpreter, bootstrap, or bootstrap/runtime
  changes into this goal merely to produce a new runtime.
- Preserve real-device, hosted-WM, performance, and QEMU gates independently
  of focused host execution.

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
| REQ-014 | blocked | B–E generation / F audit | among 34 changed/new specs, 14 mirrors are missing, 20 are stale, zero are current, and no retained log proves `0 stubs` | deployed pure-Simple runtime; run all 34 docgen commands below; review manuals | `/root` |
| REQ-015 | active | C shaping/material/config | aggregate surfaces and focused config specs cover identity, policies, target order and pre-mutation rejection; working changes canonicalize HIP to ROCm on the prepared batch | batch change is unverified; deployed pure-Simple runtime required; run aggregate/C commands | `/root` |
| REQ-016 | active | C shaping/material | source integration covers GSUB 1–8, GPOS 1–9, LookupFlag/GDEF filtering, FeatureVariations, Device/VariationIndex and anchors, named context/data facades, nested contextual remaps, ppem/coordinates/LangSys, pixel/design-unit separation, and fail-closed selected preprocessing; focused regressions cover the reviewed P1s | execute all focused specs on an admitted pure-Simple CLI and regenerate/review all affected manuals | `/root` |
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

The authoritative inventory contains 34 executable specs changed or added since
`origin/main`, after excluding the compiler-only specs and adding the focused
runner contract, SimpleOS producer/consumer artifact-root contract, four
REQ-016 full-layout specs, and changed selected-Devanagari policy spec.
Fourteen mirrored manuals are missing, 20 are
present but stale, zero are current, and zero retained owner docgen `{out,err}`
files exist. Therefore all 34 require focused deployed-runtime docgen
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

Fourteen changed/new specs currently lack mirrors:

- `doc/06_spec/01_unit/lib/test_runner_result_wrapper_spec.md`
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

Twenty existing mirrors are stale because their executable sources changed in this
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
- `simpleos_wm_qemu_evidence_contract_spec.md`
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
selected-Devanagari policy spec and omitted the two evidence-contract specs, so
they are not current 34-source evidence; lane F must audit all 34 sources after
an admitted runtime is available.
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

The four new full-layout specs, changed selected-Devanagari policy spec, focused
runner contract, and SimpleOS artifact-root contract raise the changed/new
manual scope to 34: 14 mirrors are absent and 20 are
stale. The previous title-coverage split is invalidated by the newly changed
specs. `font_asset_manifest_spec.md` and
`gui_entry_desktop_production_render_contract_spec.md` explicitly identify
themselves as manually synchronized/docgen-pending. Hand synchronization is not
generated evidence. The 14 absent mirrors and all 20 stale mirrors therefore
remain rejected until deterministic docgen succeeds with `0 stubs`.

Nine additional changed compiler/bootstrap specs are prerequisite-enablement
regressions, not shared-font requirement evidence, and are explicitly excluded
from the 34-manual and 39-command font graphs:
`bootstrap_main_source_spec.spl`,
`cli_native_build_main_contract_spec.spl`,
`interpreter_backend_spec.spl`,
`hir_lowering_error_collection_spec.spl`,
`bootstrap_expr_stmt_arena_spec.spl`,
`hir_block_tail_invariants_source_spec.spl`,
`const_eval_spec.spl`,
`effect_inference_spec.spl`, and
`resolve_nil_guard_spec.spl`. During this audit, two apparent further diffs
came only from newer upstream GPU-wire changes:
`processing_cpu_fallback_daemon_wire_spec.spl` and
`simpleos_qemu_host_gpu_2d_spec.spl`. Neither contains a font or glyph
acceptance row, neither is branch-authored shared-font evidence, and both are
excluded from this scope; the completion-time rebase absorbs that upstream
drift. Thus the authoritative feature scope remains 34, not 36.

## Exact owner commands

The authoritative docgen scope is the 34 changed/new specs classified above.
Each source owner retains the command, stdout, stderr, exit, and output-manual
hash under an immutable attempt directory; lane F audits all 34.

All retained paths are below
`build/test-artifacts/shared_multilingual_gpu_fonts/`. The exact deterministic
input set and immutable runner are frozen below. This command has not been run
and does not imply generated evidence:

```bash
set -euo pipefail
: "${CLI:?set CLI to the deployed pure-Simple runtime}"
: "${CLI_SHA:?set CLI_SHA to the admitted CLI SHA-256}"
: "${CORE_C_DIR:?set CORE_C_DIR to the matching core-C directory}"
: "${CORE_C_SHA:?set CORE_C_SHA to the admitted core-C archive SHA-256}"
: "${CHECKPOINT_SHA:?set CHECKPOINT_SHA to the clean source checkpoint}"
: "${DOCGEN_ATTEMPT:=1}"
case "$DOCGEN_ATTEMPT" in
  1|2|3) ;;
  *) echo "invalid docgen attempt: $DOCGEN_ATTEMPT" >&2; exit 2 ;;
esac
[ "$(git rev-parse HEAD)" = "$CHECKPOINT_SHA" ]
[ -z "$(git status --porcelain --untracked-files=normal)" ]
[ "$(sha256sum "$CLI" | awk '{print $1}')" = "$CLI_SHA" ]
[ "$(sha256sum "$CORE_C_DIR/libsimple_runtime.a" | awk '{print $1}')" = "$CORE_C_SHA" ]
DOCGEN_ROOT="build/test-artifacts/shared_multilingual_gpu_fonts/docgen/attempt-$DOCGEN_ATTEMPT"
mkdir -p "$DOCGEN_ROOT"

run_docgen_spec() {
  spec=$1
  name=${spec#test/}
  name=${name//\//_}
  manual="doc/06_spec/${spec#test/}"
  manual=${manual%.spl}.md
  base="$DOCGEN_ROOT/$name"
  for suffix in command out err exit manual.sha256; do
    if [ -e "$base.$suffix" ]; then
      echo "refusing duplicate docgen execution: $spec" >&2
      return 125
    fi
  done
  spec_sha=$(sha256sum "$spec" | awk '{print $1}')
  manual_before=missing
  if [ -f "$manual" ]; then
    manual_before=$(sha256sum "$manual" | awk '{print $1}')
  fi
  {
    printf 'checkpoint_sha=%s\ncheckpoint_clean=true\nattempt=%s\n' \
      "$CHECKPOINT_SHA" "$DOCGEN_ATTEMPT"
    printf 'cli=%s\ncli_sha256=%s\n' "$CLI" "$CLI_SHA"
    printf 'core_c_dir=%s\ncore_c_sha256=%s\n' "$CORE_C_DIR" "$CORE_C_SHA"
    printf 'spec=%s\nspec_sha256=%s\n' "$spec" "$spec_sha"
    printf 'manual=%s\nmanual_before_sha256=%s\n' "$manual" "$manual_before"
    printf 'command'
    printf ' %q' "$CLI" spipe-docgen "$spec" --output doc/06_spec --no-index
    printf '\n'
  } >"$base.command"
  if [ "$(sha256sum "$CLI" | awk '{print $1}')" != "$CLI_SHA" ] ||
      [ "$(sha256sum "$CORE_C_DIR/libsimple_runtime.a" | awk '{print $1}')" != "$CORE_C_SHA" ]; then
    rc=1
    : >"$base.out"
    printf '%s\n' "admitted CLI/core-C changed before docgen" >"$base.err"
  elif "$CLI" spipe-docgen "$spec" --output doc/06_spec --no-index \
      >"$base.out" 2>"$base.err"; then
    rc=0
  else
    rc=$?
  fi
  if [ "$rc" -eq 0 ] &&
      ! grep -Eq '^DONE Generated [0-9]+ docs \([0-9]+ complete, 0 stubs\)$' "$base.out"; then
    rc=1
  fi
  if [ "$rc" -eq 0 ] && [ ! -f "$manual" ]; then
    rc=1
  fi
  manual_after=missing
  if [ "$rc" -eq 0 ]; then
    manual_after=$(sha256sum "$manual" | awk '{print $1}')
    if [ "$manual_before" != missing ] &&
        [ "$manual_after" = "$manual_before" ]; then
      printf '%s\n' "docgen left a stale manual unchanged" >>"$base.err"
      rc=1
    fi
  fi
  if [ "$rc" -eq 0 ] &&
      { [ "$(sha256sum "$spec" | awk '{print $1}')" != "$spec_sha" ] ||
        [ "$(sha256sum "$CLI" | awk '{print $1}')" != "$CLI_SHA" ] ||
        [ "$(sha256sum "$CORE_C_DIR/libsimple_runtime.a" | awk '{print $1}')" != "$CORE_C_SHA" ]; }; then
    rc=1
  fi
  if [ "$rc" -eq 0 ]; then
    printf 'manual_sha256=%s\n' \
      "$manual_after" >"$base.manual.sha256"
  fi
  printf '%s\n' "$rc" >"$base.exit"
  if [ "$rc" -ne 0 ]; then
    return "$rc"
  fi
}

while IFS= read -r spec; do
  run_docgen_spec "$spec"
done <<'SPECS'
test/01_unit/app/release/install_font_assets_spec.spl
test/01_unit/app/release/release_archive_layout_spec.spl
test/01_unit/lib/common/encoding/font_asset_manifest_spec.spl
test/01_unit/lib/common/text_layout/font_render_config_spec.spl
test/01_unit/lib/common/text_layout/font_renderer_spec.spl
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_result_spec.spl
test/01_unit/lib/test_runner_result_wrapper_spec.spl
test/01_unit/lib/skia/ot_layout_apply_spec.spl
test/01_unit/lib/skia/ot_layout_gsub_full_spec.spl
test/01_unit/lib/skia/ot_layout_gpos_spec.spl
test/01_unit/lib/skia/ot_layout_gpos_full_spec.spl
test/01_unit/lib/skia/ot_layout_gpos_variation_spec.spl
test/01_unit/lib/skia/ot_layout_lookup_flags_spec.spl
test/01_unit/lib/skia/ot_layout_pinned_inventory_spec.spl
test/01_unit/lib/skia/ot_parser_layout_selector_spec.spl
test/01_unit/lib/skia/ot_parser_spec.spl
test/01_unit/lib/skia/selected_devanagari_spec.spl
test/01_unit/lib/skia/shaper_spec.spl
test/01_unit/os/gui_entry_desktop_production_render_contract_spec.spl
test/01_unit/os/drivers/framebuffer/simpleos_wm_qemu_evidence_contract_spec.spl
test/01_unit/os/port/simpleos_font_bundle_spec.spl
test/02_integration/os/port/simpleos_font_asset_staging_spec.spl
test/02_integration/rendering/wm_nested_content_frame_spec.spl
test/03_system/app/simple_2d/feature/legacy_web_gui_wm_font_route_spec.spl
test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl
test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl
test/03_system/app/simple_2d/feature/shared_font_shaping_acceptance_spec.spl
test/03_system/app/simple_2d/feature/shared_font_surfaces_spec.spl
test/03_system/app/simple_web/feature/web_font_rendering_surface_spec.spl
test/03_system/gui/feature/gui_font_event_surface_spec.spl
test/03_system/gui/linux_hosted_wm_live_window_spec.spl
test/03_system/os/wm/rv64_simpleos_wm_font_input_spec.spl
test/03_system/os/wm/simpleos_wm_fullscreen_spec.spl
test/05_perf/graphics_2d/shared_multilingual_gpu_fonts_perf_spec.spl
SPECS
```

Lane A records the deployed pure-Simple runtime and matching core-C identity
used for focused checks. Rust-seed Stage2 generation is bootstrap-only
enablement; a Rust binary or exit `2`, `124`, `132`, or `139` remains
non-evidence.

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
set -euo pipefail
ESSENTIAL_ROOT=build/test-artifacts/shared_multilingual_gpu_fonts/essential-tools
mkdir -p "$ESSENTIAL_ROOT"
for artifact in \
    identity.env command out err exit summary.env evidence.sha256; do
  if [ -e "$ESSENTIAL_ROOT/$artifact" ]; then
    echo "refusing duplicate essential-tools admission: $ESSENTIAL_ROOT/$artifact" >&2
    exit 125
  fi
done
[ "$(git rev-parse HEAD)" = "$CHECKPOINT_SHA" ]
[ -z "$(git status --porcelain --untracked-files=normal)" ]
CLI_ACTUAL_SHA=$(sha256sum "$CLI" | awk '{print $1}')
[ "$CLI_ACTUAL_SHA" = "$CLI_SHA" ]
CORE_C_ACTUAL_SHA=$(sha256sum "$CORE_C_DIR/libsimple_runtime.a" | awk '{print $1}')
[ "$CORE_C_ACTUAL_SHA" = "$CORE_C_SHA" ]
{
  printf 'checkpoint_sha=%s\ncheckpoint_clean=true\n' "$CHECKPOINT_SHA"
  printf 'cli=%s\ncli_sha256=%s\n' "$CLI" "$CLI_SHA"
  printf 'core_c_dir=%s\ncore_c_sha256=%s\n' "$CORE_C_DIR" "$CORE_C_SHA"
} >"$ESSENTIAL_ROOT/identity.env"
{
  printf 'command env SIMPLE_BINARY=%q sh %q\n' \
    "$CLI" scripts/check/check-bootstrap-essential-tools-smoke.shs
} >"$ESSENTIAL_ROOT/command"
if SIMPLE_BINARY="$CLI" sh scripts/check/check-bootstrap-essential-tools-smoke.shs \
    >"$ESSENTIAL_ROOT/out" 2>"$ESSENTIAL_ROOT/err"; then
  essential_rc=0
else
  essential_rc=$?
fi
printf '%s\n' "$essential_rc" >"$ESSENTIAL_ROOT/exit"
[ "$essential_rc" -eq 0 ]
[ "$(sha256sum "$CLI" | awk '{print $1}')" = "$CLI_SHA" ]
[ "$(sha256sum "$CORE_C_DIR/libsimple_runtime.a" | awk '{print $1}')" = "$CORE_C_SHA" ]
for marker in \
    essential_test_runner_smoke=true \
    essential_lint_smoke=true \
    essential_duplicate_checker_smoke=true \
    bootstrap_essential_tools_smoke=true; do
  [ "$(grep -Fxc "$marker" "$ESSENTIAL_ROOT/out")" -eq 1 ]
done
printf 'status=pass\n' >"$ESSENTIAL_ROOT/summary.env"
(
  cd "$ESSENTIAL_ROOT"
  sha256sum identity.env command out err exit summary.env
) >"$ESSENTIAL_ROOT/evidence.sha256"
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
set -euo pipefail
CAL_ROOT=build/test-artifacts/shared_multilingual_gpu_fonts/runner-calibration
mkdir -p "$CAL_ROOT"
for artifact in \
    identity.env fail.command fail.out fail.err fail.exit \
    empty.command empty.out empty.err empty.exit summary.env evidence.sha256; do
  if [ -e "$CAL_ROOT/$artifact" ]; then
    echo "refusing duplicate runner calibration: $CAL_ROOT/$artifact" >&2
    exit 125
  fi
done
[ "$(git rev-parse HEAD)" = "$CHECKPOINT_SHA" ]
[ -z "$(git status --porcelain --untracked-files=normal)" ]
CORE_C_ACTUAL_SHA=$(sha256sum "$CORE_C_DIR/libsimple_runtime.a" | awk '{print $1}')
[ "$CORE_C_ACTUAL_SHA" = "$CORE_C_SHA" ]
RUNNER_SHA=$(sha256sum src/app/test/font_evidence_runner.spl | awk '{print $1}')
FAIL_FIXTURE_SHA=$(sha256sum scripts/check/fixtures/font_evidence_runner_fail_spec.spl | awk '{print $1}')
EMPTY_FIXTURE_SHA=$(sha256sum scripts/check/fixtures/font_evidence_runner_empty_spec.spl | awk '{print $1}')
{
  printf 'checkpoint_sha=%s\ncheckpoint_clean=true\n' "$CHECKPOINT_SHA"
  printf 'cli=%s\ncli_sha256=%s\n' "$CLI" "$CLI_SHA"
  printf 'core_c_dir=%s\ncore_c_sha256=%s\n' "$CORE_C_DIR" "$CORE_C_SHA"
  printf 'runner_sha256=%s\n' "$RUNNER_SHA"
  printf 'fail_fixture_sha256=%s\nempty_fixture_sha256=%s\n' \
    "$FAIL_FIXTURE_SHA" "$EMPTY_FIXTURE_SHA"
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
grep -Fqx 'error: test-runner: spec failed' "$CAL_ROOT/fail.out"
grep -Fqx 'error: test-runner: no examples executed' "$CAL_ROOT/empty.out"
{
  printf 'status=pass\n'
  printf 'fail_exit=1\nempty_exit=1\n'
} >"$CAL_ROOT/summary.env"
(
  cd "$CAL_ROOT"
  sha256sum \
    identity.env fail.command fail.out fail.err fail.exit \
    empty.command empty.out empty.err empty.exit summary.env
) >"$CAL_ROOT/evidence.sha256"
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
set -euo pipefail
: "${CLI:?set CLI to the admitted pure-Simple runtime}"
: "${CLI_SHA:?set CLI_SHA to the admitted CLI SHA-256}"
: "${CORE_C_DIR:?set CORE_C_DIR to the matching core-C directory}"
: "${CORE_C_SHA:?set CORE_C_SHA to the admitted core-C archive SHA-256}"
: "${CHECKPOINT_SHA:?set CHECKPOINT_SHA to the clean source checkpoint}"
[ "$(git rev-parse HEAD)" = "$CHECKPOINT_SHA" ]
[ -z "$(git status --porcelain --untracked-files=normal)" ]
[ "$(sha256sum "$CLI" | awk '{print $1}')" = "$CLI_SHA" ]
[ "$(sha256sum "$CORE_C_DIR/libsimple_runtime.a" | awk '{print $1}')" = "$CORE_C_SHA" ]
RUNNER_SOURCE=src/app/test/font_evidence_runner.spl
RUNNER_SHA=$(sha256sum "$RUNNER_SOURCE" | awk '{print $1}')
FOCUSED_ROOT=build/test-artifacts/shared_multilingual_gpu_fonts/focused
FOCUSED_ATTEMPT=${FOCUSED_ATTEMPT:-1}
case "$FOCUSED_ATTEMPT" in
  1|2|3) ;;
  *) echo "invalid focused attempt: $FOCUSED_ATTEMPT" >&2; exit 2 ;;
esac

run_focused_spec() {
  spec=$1
  if [ "$(git rev-parse HEAD)" != "$CHECKPOINT_SHA" ] ||
      [ -n "$(git status --porcelain --untracked-files=normal)" ]; then
    echo "refusing focused execution outside the clean checkpoint: $spec" >&2
    return 126
  fi
  name=${spec#test/}
  name=${name//\//_}
  spec_sha=$(sha256sum "$spec" | awk '{print $1}')
  root="$FOCUSED_ROOT/attempt-$FOCUSED_ATTEMPT"
  mkdir -p "$root"
  for suffix in command out err exit; do
    if [ -e "$root/$name.$suffix" ]; then
      echo "refusing duplicate focused execution: $spec" >&2
      return 125
    fi
  done
  {
    printf 'checkpoint_sha=%s\ncheckpoint_clean=true\nattempt=%s\n' \
      "$CHECKPOINT_SHA" "$FOCUSED_ATTEMPT"
    printf 'spec=%s\nspec_sha256=%s\nrunner_sha256=%s\n' \
      "$spec" "$spec_sha" "$RUNNER_SHA"
    printf 'cli=%s\ncli_sha256=%s\ncore_c_dir=%s\ncore_c_sha256=%s\n' \
      "$CLI" "$CLI_SHA" "$CORE_C_DIR" "$CORE_C_SHA"
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
  if [ "$(git rev-parse HEAD)" != "$CHECKPOINT_SHA" ] ||
      [ -n "$(git status --porcelain --untracked-files=normal)" ]; then
    rc=1
  fi
  if [ "$rc" -eq 0 ] &&
      { [ "$(sha256sum "$spec" | awk '{print $1}')" != "$spec_sha" ] ||
        [ "$(sha256sum "$RUNNER_SOURCE" | awk '{print $1}')" != "$RUNNER_SHA" ] ||
        [ "$(sha256sum "$CLI" | awk '{print $1}')" != "$CLI_SHA" ] ||
        [ "$(sha256sum "$CORE_C_DIR/libsimple_runtime.a" | awk '{print $1}')" != "$CORE_C_SHA" ]; }; then
    rc=1
  fi
  if [ "$rc" -eq 0 ] &&
      ! grep -Fq 'test-runner: native result wrapper complete' "$root/$name.out"; then
    rc=1
  fi
  printf '%s\n' "$rc" >"$root/$name.exit"
  if [ "$rc" -ne 0 ]; then
    return "$rc"
  fi
}
```

Attempt 1 is the only initial execution. Attempts 2 and 3 are reserved for an
owner repair that changes the failing source; an unchanged green or unchanged
failure is never rerun. The command, both streams, and exit code remain
immutable under the attempt directory. Focused execution starts from the clean
checkpoint before docgen writes any manuals.

Before any lane relies on the helper, run its changed source contract once:

```bash
run_focused_spec test/01_unit/lib/test_runner_result_wrapper_spec.spl
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
run_focused_spec test/01_unit/os/drivers/framebuffer/simpleos_wm_qemu_evidence_contract_spec.spl
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

The authoritative command graph contains 39 unique focused executions: one
runner preflight, 6 in B, 17 in C, 11 in D including its Engine2D prerequisite
and SimpleOS artifact-root contract, and 4 in E. No path appears in more than
one group.

Each of the 34 docgen commands must exit zero and report the affected spec
complete with `0 stubs`. The owner retains the immutable identity, command,
both streams, exit, and manual hash; lane F reviews the generated operator
flow.

## Final gates owned by `/root`

```bash
find doc/06_spec -name '*_spec.spl' -print
sh scripts/audit/direct-env-runtime-guard.shs --working
sh scripts/audit/direct-env-runtime-guard.shs --staged
sh scripts/audit/numbered-artifact-guard.shs --working
sh scripts/audit/numbered-artifact-guard.shs --staged
git diff --check
bash scripts/check/check-shared-multilingual-font-evidence.shs
```

The first command must print nothing. The final command revalidates and
hash-seals exactly 39 focused artifact sets, 34 docgen/manual records, the
essential-tools admission, and the runner calibration, then verifies the new
seal before reporting PASS. Existing-seal mode is reserved for a later
independent audit and must not be invoked immediately as a redundant rerun.
Final verification remains `STATUS: FAIL`
until every blocked row has authoritative evidence; unavailable hardware stays
a blocker rather than a synthetic or static PASS.

## 2026-07-27 final compiler-enablement cycle

The minimal native-arena fix and its two regressions passed independent static
review with no P0/P1 finding. The final allowed retained-Stage3 generation
cycle exported `SIMPLE_NATIVE_ARENA_DECLS=1`, eliminating the earlier NUL
environment panic. It then stopped with exit 132 at RIP `0x88034b`, the
`_format_hir_lowering_error+0x7b` nil trap: the obsolete `rt_for_iterable`
collector passed a nonnil `LoweringError` whose `span` was nil before
`err.span.file`. This is distinct from the earlier full-CLI MethodResolver trap
at RIP `0x559924`; the current typed indexed collector was absent from the
executing Stage3 producer. Its private cache still contains 675 objects and no
candidate ELF was created. Evidence is retained at
`/tmp/simple-cli-admission-20260727-6.isfZoU/build/mini_builds/minimal_repaired_compiler_final_fb09.log`
(SHA-256
`5cd89facfb881ee5a5f5003941e9bdf486f87b90dc0fe36573ec6e7482b5e034`).
The hard three-cycle cap prevents another build in this verification window;
the 39 focused runs, 34 docgens, and essential-tools smoke remain blocked.
The only authoritative resume contract is the fresh Rust-seed Stage2 →
pure-Simple Stage3 plan in
`doc/03_plan/agent_tasks/shared_multilingual_gpu_fonts_all_items_2026-07-26.md`;
the older bridge/cache imperatives above are retained as history only.

## 2026-07-28 latest incremental profile

The branch was incrementally rebuilt on `origin/main` base `958db10638d`.
Pure-Simple Stage3 passed with 45 compiled, 647 cached, zero failed in 194.9s;
binary SHA-256:
`a920123d919c4a4c384161e16fe35a1853d6e3da6bfd3a4a4e7291a2c072f04d`.
The third and final Stage4 cycle found 1,340 unique sources and reached 50 HIR
modules by 15m38s. The local-symbol retention fix reduced observed RSS from
about 21.7 GiB in the prior run to about 7.0 GiB, but eager package-sibling
registration remained non-convergent. No full CLI, essential-tools smoke,
focused font execution, or docgen result exists. Retained log:
`build/native_probe/rebased-stage4-cycle3-final.log` (SHA-256
`92efd6d06e9c5e27ad45e98f472a953873bc78943bed43e2cb3e5855f2656fea`).
Afterward the source branch was completion-time rebased onto newer
`origin/main` base `9c19489a6e6`; no fourth build is permitted.
The remaining compiler performance blocker is tracked in
`doc/08_tracking/bug/stage4_low_memory_rss_growth_2026-07-18.md`.

`STATUS: FAIL`
