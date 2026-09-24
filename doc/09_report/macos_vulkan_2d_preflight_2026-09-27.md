# macOS Vulkan 2D preflight — 2026-09-27

Stage-2 device admission preflight for the Kimi handoff plan
(`doc/03_plan/agent_tasks/simple_2d_skia_renderdoc_kimi_handoff_2026-09-27.md`).
The 2026-09-26 audit could not run this preflight because its command sandbox
denied Metal/IORegistry access; the denial was environmental, not a renderer
verdict. In the 2026-09-27 Kimi session process both probes succeed.

## Metal

- Device: Apple M4 (`system_profiler SPDisplaysDataType`: Metal Support: Metal 4)
- Aqua session active; `AGXAcceleratorG16G` present in I/O Registry.

## MoltenVK (canonical Homebrew ICD)

- `vulkaninfo --summary` exit 0 with `VK_ICD_FILENAMES=/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json`
- deviceName: Apple M4; driverName: MoltenVK 1.4.1
- deviceUUID: `0000106b-1a04-0209-0000-000000000000`
- driverUUID: `4d564b00-0000-28a1-1a04-020900000000`
- apiVersion 1.4.334, conformanceVersion 1.4.4.0

## Receipt

Machine-readable receipt with SHA-256 digests of the ICD JSON, libMoltenVK,
vulkaninfo, and the captured summary output:
`build/tmp/macos_vulkan_2d_preflight_2026-09-27/preflight.env`
(raw output beside it: `moltenvk-vulkaninfo-summary.out`).

## Environment corrections discovered (bootstrap lane)

The full-bootstrap trust-root lane initially aborted at the Rust seed-input
fingerprint (`hash-root-policy-inputs`) for two environment reasons, both
corrected without source changes:

1. `llvm-config` (Homebrew llvm 23.1.1, keg-only) was not on the lane PATH.
   Fix: prepend `/opt/homebrew/opt/llvm/bin` to PATH.
2. With the llvm feature enabled, `bootstrap_stage3_resolve_llvm_build_authority`
   binds `llvm-config --link-static --system-libs`; Homebrew emits the absolute
   token `/opt/homebrew/lib/libz3.dylib`, and the authority's absolute-path
   branch (`bootstrap_stage3_canonical_file`) refuses symlinks, so the
   fingerprint fails. Fix per the in-script contract: `SIMPLE_BOOTSTRAP_RUST_LLVM=0`
   (the nightly rust llvm-sys pin is LLVM 18 while the host provider is 23;
   the seed builds without the llvm feature and LLVM 23 stays reserved for the
   pure-Simple backends).

With both corrections the trust-root lane passes the fingerprint and starts
the Rust seed build.

## Lane coordination

A separate Claude session owns a bootstrap lane from a clean snapshot worktree
(`/private/tmp/simple-mac-bootstrap-20260927`,
`--full-bootstrap --stop-after-stage2 --mode=dynload --jobs=10
--produce-stage3-receipt=verify-landed-compiler-fix`). Its 2026-09-27 run2
aborted at the Stage 2 pre-exec boundary: the child env omitted the six
canonical macOS toolchain assignments (`CC`, `CXX`, `AR`, `LD`, `LLVM_CONFIG`,
`SIMPLE_LLVM_REQUIRED_VERSION`) that
`bootstrap_stage3_stage2_canonical_env_names` requires on Darwin (see
`doc/08_tracking/bug/macos_stage2_canonical_toolchain_env_missing_2026-09-22.md`).
A corrected Kimi lane now runs in the shared worktree with the pinned LLVM
23.1.1 Cellar tools exported (`clang`, `clang++`, `llvm-ar`, `ld64.lld` from
lld 23.1.1, `llvm-config`, `SIMPLE_LLVM_REQUIRED_VERSION=23.1.1`,
`--backend=cranelift`, log `build/bootstrap-lane-logs/stage2-trust-root-2026-09-27-run2.log`,
output root `build/bootstrap/stage2-trust-root-2026-09-27`). The other session
relaunched (run3) without the toolchain pins and is expected to refuse at the
same gate; the Kimi lane is the one configured to proceed past it.

Update (2026-09-27 ~17:15): the Kimi lane passed all four Rust authority
builds and its seed sanity checks; Stage 2 is next. The other session's run3
got past pre-exec (pins fixed) but its Stage 2 then failed with exit 89 and no
diagnostic in any of its 9 logs — a silent kill, consistent with memory
pressure from concurrent full bootstraps on this 24 GB host (a third,
unrelated sosix lane also ran). **Coordination rule going forward: at most one
full bootstrap at a time on this host.** No relaunch of a competing lane
should occur until the running lane records a VERDICT.

Update (2026-09-27 ~17:35): the Kimi lane's Stage 2 never started — the lane
aborted with "source, Git state, configuration, seed, or checker changed
during preflight" because the shared worktree is being edited live by many
sessions and the bootstrap's mid-flight drift check fired. The Kimi lane was
relaunched from a **clean snapshot worktree**
`/private/tmp/simple-kimi-bootstrap-2026-09-27` (git worktree at `664c80efda5`,
log `/private/tmp/simple-kimi-bootstrap-2026-09-27-run.log`, same pinned
toolchain env and `--jobs=4`). The other session's run4 and an unrelated sosix
lane also run concurrently; memory pressure remains the top failure risk.

Update (2026-09-27 ~17:55): the other session's run4 also aborted at Stage 2.
Its diagnosis (now a landed fix, #1785, in its own worktree): the bootstrap
passes all six tool names even when blank, and blank values used to take the
pinned path, failing after 922 compiled units with "pinned macOS LLVM tool
must be absolute: clang++"; blank now means unpinned. The Kimi lane exports
non-blank absolute pinned values, so it is on the supported pinned path and
remains the lane expected to admit Stage 2.

Update (2026-09-27 ~18:05): the Kimi lane (then at snapshot `664c80efda5`)
failed the pre-Stage-2 `macos-cocoa-owner` audit: at that commit the
`_rt_cocoa_*` symbols are still embedded in `libsimple_native_all.a` (25
definitions) and absent from `libsimple_runtime.dylib` (0 exports), the
inverse of the required dynamic-provider layout. The fix is on current main
(origin/main was 1013 commits ahead). The Kimi snapshot worktree was moved to
`origin/main` (`4f0c08c3107`, includes #1785), the stale output root removed
(authority dirs are mode `dr-x------`; required `chmod -R u+w` first), and the
trust-root lane relaunched
(log `/private/tmp/simple-kimi-bootstrap-2026-09-27-run2.log`).

Update (2026-09-27 ~18:25): on origin/main the lane passed the
`macos-cocoa-owner` audit (`macOS Cocoa runtime ownership: PASS` — cocoa
symbols now export from the runtime dylib only) and Stage 2 self-hosted
compilation has started
(`stage2-native-build.log`). This is the long phase; the next checkpoints are
the Stage 2 sanity/provenance receipts under
`stage3/aarch64-apple-darwin/stage2-admitted/`.

Update (2026-09-27 ~19:00): Stage 2 compiled and was **admitted**
(`stage3/aarch64-apple-darwin/stage2-admitted/simple`,
candidate_sha256 `7620bf8fedc86fddc6e89facdb11aab193399c33910962f1fbbb5450e7d401cf`,
plus `admission.env` and the runtime capsule) — but the lane then ABORTED at
the Stage 2 compiler-test matrix: some spec rows delegate to the seed driver
with MC/DC off, which the runner admits only under a recorded waiver
(`SIMPLE_MCDC_OFF_WAIVER_REASON/REVIEWER/REVIEW_ID/VERSION`, atoms that "come
from the caller (the owner's approval record) and are never defaulted").
Fabricating a waiver was rejected. The supported honest alternative is
`BOOTSTRAP_STAGE2_TEST_DELEGATE=0` (rows run un-delegated under the admitted
stage-2 CLI). The lane was relaunched with that setting; the Rust authority
stamp and the stage-2 native cache are retained, so the recompile is
incremental. Stage 3 must not be resumed from this output until the test
matrix passes, per the lane's own warning.

Update (2026-09-27 ~19:20): run3 (with `BOOTSTRAP_STAGE2_TEST_DELEGATE=0`)
rebuilt the identical candidate (same sha256 `7620bf8f…` — cache hit) but
failed in a different place: the `check-bootstrap-stage2-struct-receiver`
probe saw the stage-2 compiler die with **SIGBUS (Bus error 10, status 138)**
on a bounded 5-second route fixture build. Reproducing that exact probe
standalone against the rejected candidate binary passed cleanly
(`bootstrap_stage2_struct_receiver=PASS`, `positional_stage3_route=PASS`,
~26 s), so the SIGBUS was transient — consistent with the concurrent-lane
load (5 bootstrap processes from 3 sessions were live). Run4 relaunched with
the same corrected environment; if the same probe dies again while its
standalone run passes, the transient-excuse fails and this becomes a recorded
environment blocker instead of further retries.

Update (2026-09-27 ~19:40): run4 passed the struct-receiver probe
(transience confirmed) and the admission was republished, but the matrix row
`compiler_cli_build` then **failed at the final link**: 20 undefined symbols
(`--error-limit` truncated the list; the filed bug counts 170 with
`--error-limit=0`) — `rt_sdl_*`, `rt_cuda_*`, `_text_list_contains` — all
hosted-provider ABI symbols. Root cause chain (verified against source): the
row builds the full CLI with `--runtime-bundle host-gpu` under
`SIMPLE_NO_STUB_FALLBACK=1`; the lane links only a core-C supplement (the
seed-side `build_c_runtime_library` list omits `runtime_sdl2`/`runtime_dynload`)
plus the hosted-runtime rlib, which defines **zero** `rt_*` symbols (all 1780
live in `libsimple_runtime.dylib`, which the lane does not link). The
pure-Simple core list (`runtime_compiler.spl:569`) *would* provide
`runtime_sdl2/rocm/renderdoc`, but the row drives the Rust pipeline embedded in
the candidate binary, whose lane is the narrower one.

This is a **known, owner-decision-blocked gap**, independently found and filed
30 minutes earlier by the parallel session:
`doc/08_tracking/bug/macos_stage2_compiler_cli_build_host_gpu_link_2026-09-27.md`
(landed as `0c62855cd99`, PR #1804). That bug records: the Stage 2 matrix has
not passed on any platform yet (Linux fails even earlier, at HIR field
inference); fixing requires deciding the full-CLI provider set for host-gpu on
Darwin (std shim + GPU/font providers, or a different lane) plus owner
decisions on 49 unprovided symbols. **The Kimi bootstrap lane stops here per
the lane's own "do NOT resume Stage 3" rule; further lane retries cannot cross
an owner decision.** The admitted stage-2 candidate (`7620bf8f…`) and all
receipts remain on disk for the post-fix matrix re-run.

Diagnostic while parked (2026-09-27, **not admission evidence**): the negative
matcher control (`expect(1).to_equal(2)` in a two-case spec at
`/tmp/kimi-diag/`) was run under the Rust seed driver and correctly **failed**
(`expected 1 to equal 2`, `FAIL`), so the spec/matcher machinery itself is not
vacuous. The stage-2 capsule binary only implements `compile`/`native-build`
(`unknown command 'test'`), and the seed is inadmissible as Stage-1 evidence
per the handoff — the admissible control must be re-run under the deployed
pure-Simple compiler after the host-gpu provider-set fix lands and the matrix
passes.

## Prepared next gate (after Stage 2 admission)

Expected admitted-parent layout from the trust-root lane:
`build/bootstrap/stage2-trust-root-2026-09-27/stage3/aarch64-apple-darwin/stage2-admitted/simple`
beside `stage2-sanity.receipt` (`stage2-sanity: pass`, candidate hash bound).

Then the planner-admission-v2 receipt (target `//bootstrap:stage3`):

```sh
scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs \
  --target=//bootstrap:stage3 --reason=<see note> \
  --parent-compiler=build/bootstrap/stage2-trust-root-2026-09-27/stage3/aarch64-apple-darwin/stage2-admitted/simple \
  --bootstrap-output=build/bootstrap/stage2-trust-root-2026-09-27 \
  --out=build/bootstrap/planner-admission-v2-2026-09-27.env
```

Open policy note: `bootstrap_planner_v2_reason_allowed` admits only
`seed-*` reasons and `verify-landed-compiler-fix` for `//bootstrap:stage3`
(and convergence/release/DD reasons for `//bootstrap:stage4`). None is a
truthful label for this trust-root continuation lane (the seed is healthy).
Selecting a false reason is not acceptable; if no allowed reason fits, this is
a policy gap to record against the bootstrap owner rather than fudge.

Correction (2026-09-27 ~18:45): the gap applies only to a **stage3-only**
resume. The lane this goal actually needs is the **full** Stage 2→3→4 lane
with `--deploy`, whose receipt target is `//bootstrap:stage4`, and
`self-host-convergence-check` is an allowed, truthful reason for it (the run
reproduces the whole self-hosted chain from the seed). Prepared command after
Stage 2 admission:

```sh
scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs \
  --target=//bootstrap:stage4 --reason=self-host-convergence-check \
  --parent-compiler=<admitted stage2 simple> \
  --bootstrap-output=build/bootstrap/stage2-trust-root-2026-09-27 \
  --out=build/bootstrap/planner-admission-v2-2026-09-27.env

env <pinned toolchain env> sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --deploy \
  --bootstrap-receipt=build/bootstrap/planner-admission-v2-2026-09-27.env \
  --backend=cranelift --jobs=4 --no-mcp
```

Deploy output path binding (to resolve at that time): the macOS GPU 2D
evidence helper verifies the stage3 compiler at
`$ROOT_DIR/build/wm-to-i64-bootstrap/stage3/<platform>/simple`, so the
deploy lane must run in the tree that will run the evidence, or the deploy
transaction must be pointed at that root.

## Stage-1 retained-link-failure diagnosis

The isolated verifier's retained link log
(`/private/tmp/simple_2d_verifier_20260926/build/mini_builds/renderdoc_test_runner.log`)
shows unresolved `_rt_cuda_*` / `_rt_vulkan_*` arm64 symbols because its
hand-assembled core C archive omitted `runtime_dynload.o`. The shim source
exists in-tree at `src/runtime/runtime_dynload.c`; the canonical
`core-c-bootstrap` runtime bundle includes it. Re-running that same mini build
command is not useful — the correction is to build through the canonical
self-hosted native-build path produced by the bootstrap lane above.

Next gate: when the owning bootstrap lane admits Stage 2/3, produce the
planner-admission-v2 receipt, run the Stage-3/4 + deploy lane, build the
trusted macOS Vulkan 2D live driver, and run
`scripts/check/check-macos-vulkan-2d-live-evidence.shs` once on this admitted
MoltenVK device.

## Readiness record (2026-09-27, pre-build)

Checked without the self-hosted compiler; no execution claims:

- `check-macos-vulkan-2d-live-evidence.shs` preflight assets verified present:
  pinned Bungee font `assets/fonts/google-fonts/ofl/bungee/Bungee-Regular.ttf`
  matches the harness's expected byte count (118996) and SHA-256
  (`c4f5361c…66e3f`); Vulkan harness, shared harness, DrawIR fixture,
  `backend_vulkan.spl`, and the trusted native build helper all exist.
  External tools `cliclick`, `screencapture`, `osascript`, `xcrun`, `sips`
  are installed. The trusted build manifest and WM sffi dylibs are the
  remaining generated inputs, produced by the bootstrap/deploy lane.
- **RenderDoc on macOS: unavailable.** No RenderDoc application or
  `qrenderdoc`/`renderdoccmd` is installed on this host. Per the handoff
  plan, Mac captures are therefore not claimable; this is recorded here as
  the separate result the plan requires, and no image file will substitute
  for a RenderDoc capture claim.
- Scene fixtures for Stage 3 are source-complete: the qualification scene
  contract (`src/app/test/vulkan_2d_qualification/scene_contract.spl`)
  binds `01-solid-boxes`, `06-rectangular-clip`, and `02-fractional-edges`
  with the predeclared case 02 oracle digest and polygon tolerance in
  source; corpus specs exist under `test/03_system/app/ui/feature/`.

## Web/GUI source verification (2026-09-27, no execution claims)

- Web case 02 (`web_corpus_case02_gpu_projection_spec.spl`, tagged
  REQ-2D-006 / NFR-2D-002): fixture
  `test/fixtures/html_css/corpus/cases/02-fractional-edges.html` byte-hash
  matches the pinned `CASE02_SHA256`
  (`5ad0ddd4…0bfe1`). The spec pins the real producer inventory — six
  source indexes 0..5, one strict 640×480 GPU surface, the four redundant
  white backgrounds lowered to plain integer clears, and the rotated tile
  (`0xFF247BDE`) plus fractional bar (`0xFF111111`) keeping coverage-AA
  raster policy, affine transform, fractional geometry, and the 640×480
  surface clip — plus negative tests rejecting a changed fixture hash
  (`web-corpus-case02-html-sha256-mismatch`) and missing tile paint
  metadata (`missing-source-paint-style:4:border-left-width`).
- Web case 41 (`html_css_corpus_producer_spec.spl` +
  `cases/41-sticky-scroll.html`): the pinned nested element scroll resolves
  (`status=applied`, `resolved_id=scroller`, `resolved_top=125`,
  `max_top>125`, sticky child preserved, raw box unchanged), and the layout
  renderer source explicitly rejects viewport-fixed descendants of a
  scrolled element (`FixedDescendantUnsupported`) until fixed containing
  blocks are represented. The corpus rows stay `not-run` until their
  individual gates pass, per the handoff plan.
- GUI input scene (`src/lib/common/renderdoc/gui_input_scene.spl`): the
  pinned font bytes exist and match — `NotoSansMono[wdth,wght].ttf` at
  `assets/fonts/google-fonts/ofl/notosansmono/` hashes to exactly the
  pinned `GUI_INPUT_FONT_SHA256`
  (`2cb2adb3…69a081`). The scene pins its id, widget id, 160x40 extent,
  placeholder, pointer position, key sequence (`A,B,left,C`), final value
  `ACB`, and caret 2, with paint through the real
  `widget_tree_to_draw_ir` at GPU backend. Still absent (implementation
  work, needs the self-hosted compiler to run): the `31-latin-shaping`
  runner scene, the bounded private native glyph contract, and the
  independent before/after caret/pixel oracle — matching the handoff's
  Stage-4 exit-evidence list.

## MoltenVK pin + Linux test todo (2026-09-27, late)

- macOS Vulkan backend pinning is now reproducible for the optional Skia
  lane: `tools/upstream-skia-ganesh-vulkan/env-moltenvk.shs` (source-only)
  exports `VK_ICD_FILENAMES` bound to the canonical ICD
  `/opt/homebrew/etc/vulkan/icd.d/MoltenVK_icd.json` and fails closed on
  ICD/library SHA-256 drift against this receipt's digests. Verified live:
  both digests still match (`b514f516…`, `e1773b59…`). The full live
  harness already applies the identical canonical pin
  (`check-macos-gpu-2d-live-evidence.shs`).
- New tracking todo `doc/08_tracking/todo/simple_2d_linux_vulkan_tests_2026-09-27.md`
  records the full Linux Vulkan test-execution checklist (corpus rows,
  gates, RenderDoc captures); the existing
  `simple_2d_skia_renderdoc_linux_n2_2026-09-27.md` remains the
  device-qualification half and cross-links it.
- Blocker recheck: the Darwin host-gpu provider-set fix has NOT landed on
  origin/main as of this entry (`origin/main` at `fafd99a32a9`; no
  `native_project/` commits since `4f0c08c3107`; the parallel session's bug
  doc is not visible in this worktree). The bootstrap lane stays paused.

## Stage 4 source lane (2026-09-28)

With execution gated, the Stage 4 text-lane SOURCE artifacts were
implemented (execution remains blocked until the Stage-1 compiler gate
lands; nothing here is device evidence):

- `src/lib/common/renderdoc/native_glyph_contract.spl` — bounded private
  native glyph contract, format `simple-native-glyph-contract/v1`: pinned
  Noto Sans Mono bytes/sha (matches preflight), real cmap glyph ids via the
  sfnt layer (never 5×7 charset indices), 4096-glyph bound, milli-pixel pen
  chain, typed rejections for font-identity mismatch / unsupported shaping /
  flags (clip/blend/effects) / overflow / control chars, and a
  whole-composition preflight before any device work — the design-doc
  precondition for all later text worker commands.
- `src/lib/common/renderdoc/gui_input_pixel_oracle.spl` — independent
  before/after caret+pixel oracle for `gui-input-visible-160x40-v1`,
  literal-rectangle images only, caret x=19 after `A,B,left,C`; predeclared
  NFR-2D-003 tolerances 16/4 declared before any device capture.
- `src/lib/common/renderdoc/corpus_case31_oracle.spl` +
  `test/fixtures/html_css/corpus/oracles/31-latin-shaping.oracle.json` —
  `31-latin-shaping` analytic oracle (pinned source `office affine AVATAR`,
  640×480, tolerance 16/4 predeclared), manifest.sdn/manifest.json case-31
  blocks now point at the independent oracle instead of the
  chromium-differential placeholder.
- Registration: `SCENE_CORPUS_CASE31` in `scene_contract.spl`,
  `run/verify-corpus-case31` + worker names in the qualification `main.spl`.
  Both physical workers **fail closed** (`corpus-case31-physical-text-gate-absent`)
  and `scene_input_state_sha(case31)="none"` until the text producer and
  backend adapters exist — no rectangle stand-in can be submitted under the
  text fixture id.
- Specs: `web_corpus_case31_stage1_spec.spl` (REQ-2D-006/NFR-2D-003,
  contract rejection paths + oracle self-check) and a new it-block in
  `gui_widget_vulkan_producer_spec.spl`.
- Digest methodology: expected-image digests were computed by an
  independent Python replication of the exact Simple algorithms and
  validated by reproducing case01's published pin byte-for-byte; the pinned
  face has no `kern` table (GPOS only), so kern is deterministically 0 —
  documented. Oracle self-checks will confirm at first real execution.
- Diagnostic syntax smoke (`bin/release/macos-arm64/simple check`, per file,
  evidence-invalid binary): identical repo-wide pre-existing lint failure on
  untouched control files; no diagnostic names any new file.
- `doc/06_spec` `.spl` count: 0. No commits made (shared worktree).
