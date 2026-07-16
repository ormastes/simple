---
name: sp_dev
description: "SPipe dev entrypoint: refine a feature/bug/TODO into acceptance criteria, then continue through the SPipe pipeline."
---

# SP Dev -- SPipe Development Entrypoint

`/sp_dev` is the Codex entrypoint for the SPipe development workflow. The
standalone `/dev` Codex skill has been removed so development work routes
through the explicit SPipe namespace. SPipe is the runner/docgen/process layer;
SSpec is the executable `.spl` scenario authoring surface.

Use it for a feature, bug fix, refactor, or TODO that should start with SPipe
goal refinement and acceptance criteria, then continue through research, design,
SSpec scenarios executed through SPipe, implementation, refactor, verification,
and ship handoff:

```
/sp_dev <description of what to build or fix>
```

## Dispatch

Start with the SPipe dev agent instructions in `.claude/agents/spipe/dev.md`.
Use `.claude/skills/spipe.md` for SPipe test/spec conventions when the workflow
reaches specification and verification phases.

During the SPipe Refactor phase, run the doc/wiki refactor support skill at
`.claude/skills/spipe_doc_wiki_refactor.md` so stale docs, command references,
wiki-style process knowledge, and feature/layer expert links are cleaned before
final verification. Ship consumes verify evidence and must not repair stale
process docs.

Before final verification, update every process artifact that
the lane changed: generated/manual SPipe docs under `doc/06_spec`, matching
`doc/07_guide` pages, `.codex/skills/`, `.agents/skills/`, `.claude/skills/`,
`.claude/agents/spipe/`, and `.gemini/commands/` instructions. Treat stale workflow/tooling docs as
verify failures, not release cleanup. For scenario-oriented SSpec, generate the
mirrored manual doc, read it as an operator manual, and fix step names,
captures, `@inline`/`@prev` visibility, and helper names until the primary flow
is understandable without opening the source spec.

When `$sp_dev` creates requirement option docs, do not leave them as the final
state. After the user selects feature and NFR options, write the final
`doc/02_requirements/feature/<feature>.md` and
`doc/02_requirements/nfr/<feature>.md`, delete unchosen `*_options.md` files,
and refresh the matching `doc/07_guide` page before verification. A lane with
selected options but lingering "Pending Selection" docs is not complete.

Completion gate: do not mark a goal, SPipe phase, verify report, or ship lane
complete when workflow/tooling behavior changed and the matching guide, skill,
agent, command, or generated/manual spec docs are still stale. Update the docs
first, then run focused verification evidence once.

For release-bound SPipe lanes, the final test-runner evidence is
`bin/simple test test --whole --mode=interpreter`. `--whole` must retain all
spec/long-test discovery and execute both `.spl` comment doctests and configured
Markdown code fences; a narrower `--all`, `--only-slow`, or smoke run is not
release evidence.

For work spanning multiple host or capability rows, keep every unavailable
row's acceptance-criterion IDs active. Reuse its authoritative TODO and plan,
or create them when none exist, and record the missing prerequisite, exact
resume command, and retained artifacts.
Postponement is not completion: it cannot move the row into exclusions, close
its TODO, or permit a phase, verify report, or goal to be marked done. Postpone
only native execution that genuinely requires another prepared host; keep all
host-independent and current-host rows active until finished.
Keep every unavailable row visible in executable and generated-manual evidence
as `unsupported` or `blocked`; never omit it, convert it to `skip()`, or count
it as PASS. `Current-host scope complete` is narrower than feature completion.
The authoritative resume plan must name the target host/capability,
prerequisites, exact command, retained artifacts, owner, and final reviewer.

For SimpleOS QEMU host-GPU NFR-006, TODO 566 postpones only unavailable
non-current native timing rows. Hardware-independent source/parser/self-test
work and the current Linux native row remain active. Evidence must cover one
guest-observed interval from device initialization through every rejected or
timed-out Metal, DirectX, and Vulkan attempt to backend selection or CPU
fallback. Daemon HELLO `elapsed_us` and cross-ISA TCG prove correctness only,
not the 500 ms native target.

For SimpleOS compiler-in-filesystem lanes, completion requires the Simple
compiler/interpreter/loader payload to be embedded in the SimpleOS install image
and executed from the SimpleOS filesystem. SPipe specs must prove the target
payload is SimpleOS-native, not host `bin/simple`, and that the image contains
`/usr/bin/simple(.smf)`, `/bin/simple(.smf)`, `/sys/apps/simple(.smf)`,
`/sys/apps/simple_compiler(.smf)`, `/sys/apps/simple_interpreter(.smf)`,
`/sys/apps/simple_loader(.smf)`, and `/SYS/SIMPLETOOL.SDN`. A PASS claim also
needs in-guest evidence for `/usr/bin/simple --version` plus compiling and
running a small `hello world` from the mounted filesystem. QEMU fixed-command
stubs, host-side compiles, and placeholder marker apps are blockers, not proof.
Physical-board claims additionally need board identity, boot/download path, and
serial or SSH transcript; otherwise record QEMU-only or source-present status.

For recent unfinished-plan cleanup lanes, use
`doc/07_guide/infra/recent_plan_cleanup.md`. Keep the cleanup matrix under
`doc/03_plan/agent_tasks/` with sidecar lanes/`N/A`, merge owner, and final
reviewer, keep SPipe state under `.spipe/<cleanup-name>/`,
classify every candidate as `mark-done`, `needs-evidence`,
`needs-requirement-selection`, `needs-implementation`, or `superseded/merge`,
and run normal LLM review before accepting generated-manual quality, done marks,
or broad exclusions.

When implementation changes add or replace evidence wrappers, refresh the
matching guide/process documentation in the same lane. For GPU, Engine2D, Simple
Web, Electron/Tauri, QEMU, or backend readback evidence, update the relevant
`doc/03_plan`, `doc/07_guide`, and `doc/09_report` references so future agents
can find the canonical wrapper instead of repeating stale commands.
Production CUDA font loading may use only Simple-generated PTX bound to an
immutable package/tracked manifest hash and program version. Ignored `build/`
output and a caller-provided adjacent hash are evidence, not trust anchors.
For HTML-backed GUI modernization, pair screenshot or bitmap evidence with
structured Electron interaction evidence. A pass needs visible controls to
receive focus, keyboard/input, pointer, and click events, or the wrapper must
classify the missing GUI host dependency explicitly.
For RenderDoc evidence specifically, use
`scripts/tool/renderdoc-evidence.shs capture-simple` for the Simple
in-application `rt_renderdoc_*` path and
`scripts/tool/renderdoc-evidence.shs capture-html` for original
RenderDoc+Chrome HTML/CSS capture, plus
`scripts/tool/renderdoc-evidence.shs capture-electron-html` for bundled
Electron Chromium HTML/CSS capture. Tests should route through
`test/helpers/renderdoc_capture_helper.shs` or the compatibility wrappers.
For GUI/web/2D RenderDoc+Vulkan work, use
`scripts/setup/setup-gui-web-2d-vulkan-env.shs --check` for readiness,
`--browser-backing` for focused direct Electron Chromium backing proof, `--run`
for direct Electron/Chrome/Simple probes, and `--renderdoc-simple` for the
Simple in-application RenderDoc debug path on a prepared Linux or macOS
RenderDoc host. Leave `RDOC_SIMPLE_BIN` unset unless deliberately overriding;
the helper builds `src/compiler_rust/target/release/simple` so the
`rt_renderdoc_*` externs are current. Use all-lane `--renderdoc` only for
cross-surface evidence collection.
For browser RenderDoc diagnostics, `RDOC_RENDERDOC_HOOK_CHILDREN=0` omits
`--opt-hook-children`; this may isolate Chromium child-hook crashes, but it is
not passing evidence unless the Chrome/Electron GPU-process capture still emits
a valid `.rdc` with `RDOC` magic.
Do not accept `--in-process-gpu` as a Linux Chromium/Vulkan workaround unless a
fresh run proves Vulkan remains enabled and emits valid browser `.rdc` evidence;
current Electron/Chrome diagnostics show that mode is unsupported or crashes.
On Windows, first read `doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md`.
`vulkaninfo --summary` plus Chrome/Electron installation proves host readiness
only; it does not prove Chrome or Electron are Vulkan-backed. The Vulkan SDK
installer may require administrator elevation, and SDK readiness requires a
fresh shell where `glslangValidator`, `spirv-as`, and any required shader
compiler such as `dxc` resolve. If `winget install --id
KhronosGroup.VulkanSDK` reaches an elevation prompt and is canceled, record
`sdk-tools-missing` and do not claim SDK setup complete.
Install/refresh `vulkan-tools`, `vulkan-loader`,
`vulkan-headers`, `molten-vk`, `spirv-tools`, and `glslang`; prove MoltenVK
with `vulkaninfo --summary`; then require Simple Vulkan/Engine2D evidence,
original Chrome evidence, Electron Chromium evidence, and production GUI/web
parity evidence. A Chrome/Electron bitmap with a log containing Chromium's
`angle=vulkan` unavailable failure is a fallback render, not Vulkan proof;
record `vulkan-angle-unavailable` and leave the gate failed. The aggregate
audit must expose `gui_web_2d_vulkan_comparison_fixture_status`,
`gui_web_2d_vulkan_comparison_artifact_status`,
`gui_web_2d_vulkan_comparison_artifact_reason`,
`gui_web_2d_vulkan_electron_argb_viewport_match_status`,
`gui_web_2d_vulkan_electron_argb_file_status`,
`gui_web_2d_vulkan_electron_argb_nonblank_status`,
`gui_web_2d_vulkan_chrome_argb_file_status`,
`gui_web_2d_vulkan_chrome_argb_viewport_match_status`,
`gui_web_2d_vulkan_chrome_argb_nonblank_status`,
`gui_web_2d_vulkan_simple_evidence_file_status`, and
`gui_web_2d_vulkan_simple_backend_status` before treating Electron,
Chrome, and Simple artifacts as comparable. The audit may still emit
`gui_web_2d_vulkan_chrome_screenshot_*` diagnostic keys, but a missing Chrome
PNG is not a comparison blocker when the Chrome ARGB artifact is present,
viewport-matched, and nonblank.
Artifact presence is not a pixel-equivalence claim. Require
`gui_web_2d_vulkan_pixel_comparison_status=pass`,
`gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff`, ARGB metadata for
Electron/Chrome/Simple, and the zero-mismatch pairwise diff statuses
`gui_web_2d_vulkan_electron_chrome_pairwise_diff_status`,
`gui_web_2d_vulkan_electron_simple_pairwise_diff_status`, and
`gui_web_2d_vulkan_chrome_simple_pairwise_diff_status` before claiming the
Electron baseline, Chrome Vulkan-backed render, and Simple GUI/web/2D Vulkan
render match pixels. If the aggregate reports
`gui_web_2d_vulkan_pixel_comparison_status=fail` with
`gui_web_2d_vulkan_pixel_comparison_mode=pairwise-argb-diff-mismatch`, treat it
as a real pixel mismatch to fix, not as missing evidence.
Browser Vulkan proof must be read
from `gui_web_2d_vulkan_browser_backing_status`,
`gui_web_2d_vulkan_browser_backing_reason`, and
`gui_web_2d_vulkan_browser_backing_mode`; fallback bitmap comparison is not
Vulkan-backed browser proof, and the aggregate GUI audit must remain incomplete
until browser backing is `pass`. Read current macOS blocker lanes from
`gui_web_2d_vulkan_renderdoc_blocker_status`,
`gui_web_2d_vulkan_renderdoc_blocker_reason`,
`gui_web_2d_vulkan_renderdoc_blocker_gate_count`, and
`gui_web_2d_vulkan_renderdoc_blocker_gates` before claiming RenderDoc, Simple,
Electron, or Chrome Vulkan-backed capture is ready; blocker status `blocked` is
a completion blocker, not a warning. GUI widget fixture evidence must
also prove per-widget feature witnesses via
`gui_widget_rendering_fixture_coverage_renderdoc_fixture_widget_features`, not
only widget/class presence. When a task claims all GUI items are RenderDoc
tested, run `scripts/check/check-gui-widget-renderdoc-goal-status.shs`; require
`gui_widget_renderdoc_goal_status=pass`,
`gui_widget_renderdoc_goal_widget_feature_covered_count=43`,
`gui_widget_renderdoc_goal_simple_gate_status=pass`,
`gui_widget_renderdoc_goal_electron_gate_status=pass`, and
`gui_widget_renderdoc_goal_blocked_gate_count=0`. Normal non-Mac runs may report
`incomplete`, but release or completion claims must use `--strict` with real
Simple Vulkan Engine2D and Electron Chromium/Vulkan `.rdc` evidence. Defer
Windows claims until the Windows runbook validates the same evidence keys and
RDOC gate contract; Linux claims use the Linux render-log comparison below.
For Linux Vulkan render-log comparison, require the aggregate audit to expose
`linux_vulkan_render_log_compare_blocked_gate_count`,
`linux_vulkan_render_log_compare_blocked_gates`,
`linux_vulkan_render_log_compare_renderdoc_simple_env_file_status`,
`linux_vulkan_render_log_compare_renderdoc_simple_artifact_file_status`,
`linux_vulkan_render_log_compare_renderdoc_simple_artifact_magic`,
`linux_vulkan_render_log_compare_renderdoc_chrome_env_file_status`,
`linux_vulkan_render_log_compare_renderdoc_chrome_artifact_file_status`,
`linux_vulkan_render_log_compare_renderdoc_chrome_artifact_magic`,
`linux_vulkan_render_log_compare_renderdoc_electron_env_file_status`,
`linux_vulkan_render_log_compare_renderdoc_electron_artifact_file_status`, and
`linux_vulkan_render_log_compare_renderdoc_electron_artifact_magic`; an env file
that exists without a real `RDOC` artifact remains a blocker. Browser capture
failures must keep `renderdoc-chrome-rdc` and/or `renderdoc-electron-rdc`
visible in the blocked-gate list; a summarized reason alone is not enough for a
completion claim.
For SimpleOS hardening work that combines Vulkan-over-2D, RenderDoc, LLVM,
SIMD, and QEMU GPU access, use
`scripts/check/check-simpleos-hardening-evidence-matrix.shs` as the canonical
handoff aggregate. Current completion requires
`simpleos_hardening_mission_critical_release_status=pass`,
`simpleos_hardening_mission_critical_release_blockers=none`,
`simpleos_hardening_mission_critical_prereqs_status=ready`,
`simpleos_hardening_matrix_passed=26/26`,
`simpleos_hardening_riscv_rtl_sby_proof_status=pass`,
`simpleos_hardening_gui_renderdoc_vulkan_status=pass`,
`simpleos_hardening_llvm_port_status=pass`,
`simpleos_hardening_cpu_simd_status=pass`,
`simpleos_hardening_formal_lean_proofs_status=pass`,
`simpleos_hardening_formal_riscv_dual_track_status=pass`,
`simpleos_hardening_formal_critical_concurrency_status=pass`,
`simpleos_hardening_formal_memory_safety_status=pass`, and
`simpleos_hardening_formal_storage_integrity_status=pass`, plus
`simpleos_hardening_qemu_virtio_gpu_access_status=pass` and
`simpleos_hardening_stale_reports=none`; update the generated
manual for `test/03_system/gui/simpleos_hardening_evidence_matrix_spec.spl`
when that row contract changes. If `reason=stale-static-reports`, refresh the
named source reports before claiming completion. If mission-critical prereq or
RTL/SBY wrappers change, require their `--self-test` forms, and treat missing
strict RVFI readiness as a completion blocker rather than a formal proof pass.

For SimpleOS QEMU host-GPU external-host evidence, follow the postponement and
resume contract in `doc/07_guide/platform/simpleos/qemu_system_tests.md` and
the existing-TODO matrix in
`doc/03_plan/agent_tasks/simpleos_qemu_host_gpu_external_host_evidence.md`.
Postpone only prepared Windows DirectX, macOS Metal, NVIDIA CUDA, and the
non-current native-host portions of TODO 563, TODO 569, and TODO 570; their
current Linux Vulkan portions remain active.
Resume only on the prepared native host with a pure-Simple compiler accepted by
`simple_binary_is_valid`. Never promote source inspection, emulation,
screenshots, cached reports, synthetic handles, or CPU mirrors to native PASS;
require device-origin readback, stable identity, exact CPU-oracle parity,
correlated IDs, and final high-capability review.

For RV32/RV64 baremetal compiler/firmware lanes, keep runtime-value ABI fixes at
the compiler/runtime owner boundary: do not paper over `rv_type` width bugs with
firmware-local `rt_*` shims or broad all-`i64` predeclares. Add the smallest IR
regression that proves the failing scalar shape (for example RV32 call-result
`!=` literal emits `icmp`, not `rt_native_neq`) and verify both the wrapper
result marker and any subsystem serial `FAIL` lines separately. For the RV32
NVMe firmware boot wrapper, run
`sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/boot.shs --self-test` when
marker handling changes so fake-QEMU evidence proves missing PASS and serial
`FAIL` paths fail closed. Use
`sh scripts/check/check-nvme-baremetal-wrapper-coverage.shs` to expose RV32/RV64
wrapper coverage status; run `--strict` before any completion or release claim
so missing RV64 wrapper/spec coverage remains a blocker instead of becoming a
silent gap.

For Tauri2 mobile renderer parity, use
`scripts/check/check-tauri-mobile-renderer-parity-evidence.shs`. It must pass
the desktop production GUI/Web parity source first, then require live iOS
Tauri2/WKWebView screenshot evidence plus Metal markers and live Android
Tauri2/WebView screenshot evidence plus Vulkan/skiavk or host-emulator Vulkan
markers. Both mobile lanes must also expose
`*_mdi_event_status=pass`, `*_mdi_capture_status=pass`,
`*_mdi_performance_status=pass`, and `*_mdi_animation_status=pass` from the
`[tauri-shell] mdi proof:` JSON. That proof covers window-manager event
delivery, viewport capture provenance, `performance.now()`, two animation
frames, and CSS animation support. A packaged APK or a nonblank Android
screenshot is not Vulkan proof if logcat contains `F/DEBUG`, `Fatal signal`,
`VulkanManager`, `Headless UI completed`, or subprocess parse failures; leave
the aggregate unavailable/failed until the Android renderer log, screenshot,
and MDI proof all pass. Host/emulator GPU logs such as ANGLE/Vulkan or
Apple/SwiftShader Vulkan are supporting evidence only when `com.simple.ui`
remains foreground, a `[tauri-shell] render, html_len=` marker is present, the
screenshot is captured from the live app, and the MDI proof is valid.

For runtime concurrency work, keep the public API map current in
`doc/07_guide/lib/misc/stdlib.md`, `doc/07_guide/compiler/check_perf.md`, and
`.codex/skills/coding/SKILL.md`. In particular, distinguish `thread_spawn`
(OS thread), `cooperative_green_spawn` / `cooperative_green_spawn_value`
(implemented cooperative green-thread queue on the current OS thread),
`multicore_green_spawn` (Pure Simple bounded-worker facade over `rt_pool_*`),
and `task_spawn` (pool-backed native task path when `rt_pool_*` links). Do not
document cooperative green-thread APIs as Go-style M:N CPU parallelism. When a
profile or test claims M:N behavior through `multicore_green_spawn`, require
`MulticoreGreenHandle.used_runtime_pool()` evidence so inline fallback cannot
masquerade as CPU-parallel work.

For dynSMF or SMF-startup work, distinguish three separate lanes before
editing: SimpleOS disk SMF placement, GUI SMF dynlib release evidence, and the
general dynSMF background compile/startup lane. If the request says the
interpreter should compile SMF while reading/running scripts, or mentions
precompiled `build/dynsmf/*.smf` artifacts, start with
`src/os/smf/dynsmf_session.spl`,
`src/app/startup/dynsmf_autoload.spl`, and
`scripts/check/check-low-dependency-dynsmf-build-plans.shs`. This is not
GUI-only: GUI renderer entries and non-GUI entries share the same manifest,
build-plan, `compile_background` evidence, and checked-autoload contract. Update
`doc/07_guide/lib/api/dynlib_api.md`, the low-dependency dynSMF architecture
and design docs, and the matching SPipe specs whenever that contract changes.

For optimization work, use `.codex/skills/optimize/SKILL.md`. SPipe optimization
tasks must start from a baseline, run
`bin/simple run src/app/optimize/main.spl <file> --full --level=O3` on touched
`.spl` files, preserve behavior, and rerun both correctness tests and the same
perf script. Do not rewrite Simple features in C/Rust to claim C-level speed; if
parity is blocked by runtime/compiler behavior, record a measured blocker under
`doc/08_tracking/bug/`.

Minimize runtime coupling first in SPipe lanes. App, GUI, web, 2D, MCP/LSP, and
benchmark code should use Simple facades instead of new raw runtime calls,
env/CLI shortcuts, direct backend field poking, or tool-local runtime aliases.
A build-local alias entrypoint is a last-resort compatibility shim, not the
default path for new capability. If performance or correctness is blocked by
generated native code, fix the Simple compiler/codegen/runtime owner path with
the smallest reproducer and gate; only edit `src/runtime/**` when the lane is
explicitly runtime-owned or the bug is proven there. Do not hide a
compiler/runtime bug by normalizing an `rt_*` workaround in feature code.

For nil/optional failures, fix the owner lowering/type/runtime path instead of
making `nil` displayable or adding local `rt_*` shims. `nil` is absence like an
empty `Option`; SPipe scenarios should assert `to_be_nil()` or unwrap/default
before field access, method calls, or user-facing output.

Before adding any new `rt_*` import, extern, wrapper, alias, runtime-backed
fixture bypass, or direct backend field access outside `src/runtime/**`, stop
and record the decision in the lane state:

- `runtime_need`: the exact missing capability or measured bottleneck.
- `facade_checked`: the existing `std.*`, `app.*`, owner-module, or build-local
  alias facade checked first.
- `chosen_path`: `reuse-facade`, `add-smallest-owner-facade`,
  `fix-codegen-runtime-owner`, or `runtime-owned-change`.
- `rejected_shortcuts`: raw aliases, fixture-only branches, backend pokes, or
  generated-code workarounds deliberately not used.

The default chosen path is `reuse-facade`; the default answer to a new `rt_*`
shortcut is "do not add it". Add the smallest missing facade in the owner module
or improve codegen/runtime once at the owner boundary. Pixel/rendering evidence
tools may keep bounded local fixture painters, but must not grow new raw runtime
shortcuts to paper over renderer, compiler, or backend bugs. Any attempt to
solve an SPipe failure by adding `rt_*` plumbing must also add or cite a focused
gate proving the facade/codegen/runtime boundary, not just the feature output.

Before handoff, run `sh scripts/audit/direct-env-runtime-guard.shs --working`
for runtime-adjacent app/gc lanes and treat any new raw env/process runtime
imports or calls outside owner modules as a fix-before-done issue.
For process/signal hardening, also require the
`doc/07_guide/runtime/process_kill_safety.md` rule: every kill/wait path rejects
`pid <= 0` before signaling or reaping. Seed runtime changes to that guard need
`scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy` before
they affect deployed binaries.

Before touching runtime-adjacent code in an existing lane, read that lane's
recorded `rejected_shortcuts` first; do not retry a rejected `rt_*`, fixture
bypass, backend-poke, or generated-code workaround unless new evidence changes
the decision.

For runtime-vs-pure-Simple algorithm work, use the shared dual-backend mode
names consistently in specs, docs, and code:

- `alpha` = current default, run both and stop on diff
- `beta` = run both and log a critical diff report
- `normal` = run only the preferred implementation

Prefer helper names that expose those mode names directly:

- `dual_backend_alpha_default_mode()`
- `dual_backend_beta_default_mode()`
- `dual_backend_normal_pure_simple_mode()`

Keep the legacy `assert/critical/pure_simple` helper names only as temporary
compatibility aliases. New wrappers, examples, and docs should use the
`alpha/beta/normal` helper names.

For Pure Simple SSH/HTTPS server work, use `alpha`/`beta`/`release` mode names:
`release` is the production single-path Simple protocol mode, while `alpha` and
`beta` may compare against native/SFFI protocol wrappers. Runtime/SFFI may supply
host access only (TCP accept/read/write, time, entropy, filesystem/cert/key
access, and process execution). Release-mode production wrappers must not call
`rt_ssh_*` or `rt_tls_server_*` as complete protocol bypasses. Keep
`doc/07_guide/lib/networking/pure_simple_servers.md` current when this contract
changes.

For native HTTPServer/static-file performance lanes, keep the canonical evidence
set current before handoff: `scripts/check/check-native-pure-simple-goal-status.shs`,
`scripts/check/check-web-server-nginx-live-compare.shs`,
`scripts/check/check-web-server-static-external-live-compare.shs --require-simple-ge-all`,
`scripts/check/check-web-server-go-erlang-static-compare.shs --require-simple-ge`,
`scripts/check/check-httpserver-live-static.shs`, and
`scripts/check/check-httpserver-static-profile-counters.shs --broad --require-retained`.
Update `doc/07_guide/infra/testing/benchmarking.md`,
`doc/10_metrics/perf/web_server_nginx_compare.md`,
`doc/09_report/perf/web_server_nginx_compare_2026-06-17.md`, and the active
tracking docs when retained rows or wrappers change. Do not keep a
micro-optimization that fails retained rows; revert it or record the measured
blocker/rejected result under `doc/08_tracking/`.

When a task introduces a new runtime/pure wrapper, update the shared guide at
`doc/07_guide/os/crypto_dual_backend.md` and prefer an explicit
`DualBackendConfig` dependency-injection entrypoint plus a default-config
convenience wrapper. If `normal` mode is meant to avoid dual execution on the
hot path, use the `dual_backend_run_*` lambda-based helpers rather than
precomputing both outputs before comparison.

For UI, GUI, MDI/window-manager, Draw IR, Simple 2D, or Engine2D backend-lane
work, keep the stack architecture current in
`doc/04_architecture/ui/simple_gui_stack.md` and its TLDR companion. If the work
changes shared UI contracts, event propagation, Draw IR source/event metadata,
or the drawing-vs-processing backend split, update the generated/manual spec
docs under `doc/06_spec`, the relevant `doc/07_guide` process note when one
exists, and cite the canonical implementation paths such as
`src/lib/common/ui/draw_ir.spl`,
`src/lib/common/ui/window_scene_draw_ir.spl`, and
`src/lib/gc_async_mut/gpu/engine2d/backend_lane.spl`.

## Shared multilingual font work

Apply these rules to work touching bundled fonts, shaping, glyph material,
font GPU emission, or GUI/Web/2D/3D text.

1. Pin the CLDR ranking input and reproducibly regenerate the selected top ten;
   retain rank 11 only as the cutoff witness, never as a selected-language row.
2. Keep exactly ten product categories and immutable URL, revision, license,
   Reserved Font Name (RFN), hash, byte-size, embedded name, table, and
   default-axis metadata for every bundled free-font candidate.
3. Keep an honest 10x10 matrix whose only statuses are `native`, `fallback`,
   `not-designed-for-script`, and `unavailable`. Promote a cell only through an
   executable, exact-face-bound shaping and corpus gate; codepoint presence is
   not acceptance.
4. Reuse the canonical `FontRenderer`, transient `FontRenderBatch`, and common
   atlas ownership. Do not create another renderer, atlas, cache, or private
   font draw path.
5. Web and GUI producers emit `DrawIrComposition`; Engine2D lowers its text
   through `draw_text`. Engine3D HUD/world text is a separate consumer lane,
   never a shortcut for Web, GUI, Draw IR, or 2D.
   The canonical WM frame path is `SharedWmScene -> DrawIrComposition ->
   Engine2D`; `shared_wm_scene_render_*_to_backend` and `_to_pixel_buffer` are
   compatibility renderers, not equivalent completion paths. Canonical
   SimpleOS runner/readiness targets select `gui_entry_desktop.spl`; direct
   legacy `wm_entry.spl` files remain compatibility-only and are not evidence.
   Hosted `HostCompositor.render_frame_engine2d` now owns the persistent
   canonical source route. Source ownership is not executable/device proof,
   and immediate compatibility retries remain non-completion paths.
   In this lane `WebIR` means the existing web semantic/layout model; do not
   invent a second drawing IR or store glyph/atlas/native material in it.
   Producer-resolved shaping may cross Draw IR only as handle-free glyph IDs,
   positions, and logical clusters. Its SDN form must round-trip those arrays;
   `font-shaping=selected-pure-simple` without a valid payload fails closed.
   Atlases, face handles, backend resources, and caches remain transient
   `FontRenderer`/Engine2D material.
6. GPU proof climbs `emission -> compile -> submission -> fence -> device-origin
   readback -> CPU parity`; stop and report the first unavailable rung.
   `unavailable` is never PASS.
   Compile evidence must include the Simple-emitted font companion and its
   versioned exported symbol; CUDA font GPU execution and runtime promotion must
   load that verified artifact, not a handwritten or independently generated
   parallel blob.
   Vulkan promotion additionally requires the validated precompiled-SPIR-V
   artifact mode and its exact pinned hash; runtime GLSL is diagnostic execution
   only.
7. Shaping and material preparation fail closed unless every required operation
   completed and the final glyphs remain bound to the exact live face handle
   and generation.
8. Freeze these five SSpec phrases exactly:
   `Load the pinned multilingual font manifest`;
   `Accept exact-face-bound simple-script shaping`;
   `Prepare one shared font batch for 2D and 3D`;
   `Emit the selected font composite program and plan compilation`;
   `Prove native submission and device readback`.
   Mirrored manuals under `doc/06_spec` are `.md` only.
9. Lower-model sidecars may implement or audit bounded lanes and generated
   manuals, but the final done mark and manual-quality judgment require a
   higher-capability review.
10. WM/GUI/Web/2D selected-font evidence must bind Web layout and Draw IR paint
    to one stable manifest identity and the same ordered advances. Preserving
    `font-family` metadata or selecting a TTF only during paint is incomplete;
    Web producers use the HTML/WebIR-to-DrawIR owner and GUI producers use
    `widget_tree_to_draw_ir`; a private widget command collector is not evidence.
    A dispatch PASS must submit that exact composition; an unrelated frame event
    leaves dispatch `not_requested`. Preserve the executor's exact readback source.
    Unstyled legacy Draw IR must remain bitmap-compatible. A synthetic
    composition proves the contract only; production-route acceptance must
    exercise the real hosted frame owner and canonical SimpleOS entry, with
    platform backends limited to final-pixel presentation.
11. SimpleOS font-host claims must reuse `FontAssetCandidate`, stage the exact
    pinned bytes through every applicable disk/initramfs builder, and prove
    guest path/length/hash plus glyph and framebuffer evidence. Host-repository
    asset presence is not guest proof. Source wiring or a serial marker is not
    pixel proof; retain the independent QEMU `pmemsave` crop and evidence record.
12. Runtime font configuration uses the one text-layout-owned
    `FontRenderConfig` beside `FontRenderBatch`. Evidence
    must vary and assert every family/category/language/script, size,
    weight/style, hinting, antialiasing, atlas-policy, target, and execution-
    policy identity dimension through bitmap, selected-vector, shaped, 2D, and
    3D paths. `Suggested` tries the named target first, then the remaining
    canonical GPU order, then CPU; `Preferred` tries the named target then CPU;
    `Required` tries the named target only. Unsupported modes/CTM reject before
    cache/backend mutation. `Suggested(auto)` uses the engine's executable
    font-adapter order; Preferred/Required with `auto` and unknown targets
    reject before mutation. Batch evidence carries config identity, target,
    and policy; the config object never crosses WebIR or Draw IR.
13. NFR-008 promotion uses `VulkanFontCompositeEvidence` and
    `vulkan_font_stage_evidence_ready`, then persists the observation through
    `FontPerfBudgetEvidence`, `read_font_perf_evidence`, and
    `expect_font_perf_budget`. Treat `queue_device` as the fused
    submit-through-device-completion interval, never sum it with the later
    fence-observation `sync` interval, and record offscreen presentation as
    `not-applicable-offscreen` while still requiring device readback.
14. Interpreter diagnostics reuse `build_interpreter_result_wrapper` through
    the canonical test runner or `src/app/test/font_evidence_runner.spl`.
    Before trusting them, require exit 1 and the distinct canonical failure
    markers from
    `scripts/check/fixtures/font_evidence_runner_fail_spec.spl` and
    `scripts/check/fixtures/font_evidence_runner_empty_spec.spl`; reject
    2/124/139 and retain commands, binary SHA-256, and logs per `$system_test`.
    The focused runner accepts exactly `<pure-simple-bin> <spec.spl>`, never
    performs implicit binary/seed fallback, uses the existing process/file
    facades, and propagates ordinary child exit codes. For process-facade `-1`,
    it maps a timeout marker to 124 and other launch failure to 1. It preserves
    stderr and deletes its temporary wrapper.
    They never replace native evidence.

For UI-test helper work, keep the test-library surface consistent: new SSpec
manual specs use canonical `use std.spec.*` and `step("...")`, existing
`use std.spipe` remains an alias, and UI/SGTTI/Draw IR helpers must layer inside
SSpec scenarios instead of replacing `describe`, `it`, `expect`, `step`, or the
built-in matchers. `Given_*`, `When_*`, and `Then_*` helpers are legacy manual
text helpers.
SGTTI is a test/debug evidence interface. Production entrypoints must not import
`std.ui_test.sgtti`, `SgttiTestDriver`, or SGTTI capture builders unless the
specific debug/test entrypoint explicitly opts in; compile-time entry-closure
builds must be able to elide SGTTI entirely. When adding TUI/GUI debug evidence,
include a system spec that proves the normal entrypoint has no SGTTI/debug-TUI
import path.
When a UI change claims layout, border, color, style, or text-bound parity,
prefer the Protocol-v2 Draw IR baseline diff
`/api/test/draw-ir/diff?baseline=...&capability=draw_ir` or the shared
`common.ui.draw_ir_diff` helper as structured evidence before falling back to
pixel-only assertions.
When the question is "where did this GUI component render?", use
`/api/test/draw-ir/layout?id=...&capability=draw_ir` or `expect_draw` to assert
the stable id, role/kind, geometry, hit rect, parent, and computed style inside
the SSpec case.
After adding or moving UI-facing app feature specs, run
`test/03_system/app/testing/feature/ui_sspec_evidence_audit_spec.spl` to keep
the critical UI SSPEC lane mirrored into generated manuals with visible
evidence markers.

For portable processing, GPU compute, ML matops, draw-kernel, RV64GCV, VHDL/RTL
accelerator, or `simplegpu64` work, keep the processing lane current in
`doc/04_architecture/compiler/backend/processing_backend.md`,
`doc/04_architecture/compiler/backend/processing_backend_tldr.md`, and
`doc/07_guide/compiler/backends/processing_backend.md`. Treat CUDA, Vulkan,
RV64GCV, VHDL/RTL, and CPU fallback as backends below ProcessingIR, not separate
public API forks. Do not claim Simple has a real RISC-V64 Adreno/Mali-like GPGPU
until CPU oracle, software backend, and RTL/simulation evidence agree for the
same processing scenarios.

For compiler cache, loader, JIT, formal verification, or accessor-forwarding
work, include SPipe evidence for semantic invalidation. A change to public ABI,
field-wrapper shape, forwarded getter/setter behavior, or generated accessor
dependencies must miss the interpreter/incremental cache and any SMF/JIT cache
that could otherwise reuse stale code. Add focused specs near the cache owner
instead of relying only on broad loader suites.

For Lean or BYL formal-verification lanes, keep generated backend output
separate from handwritten proof additions. Regeneration should update generated
obligations without overwriting stable theorem files, and SPipe evidence should
name the generated artifact plus the durable proof entry points that must still
check after regeneration. Treat BYL as generated proof-model interchange, not
as a Lean replacement: claims are proved only by the lane's checked Lean command
or by the target hardware proof command. If a generator renames or removes an
export consumed by a manual theorem, update the generator manifest/contract and
the manual proof in the same lane before handoff. Added proof intent belongs in
manual theorem/constraint files; generated Lean or BYL files should only gain it
when the generator contract is updated in the same lane.
For RISC-V lanes that combine generated RTL sidecars with Lean/BYL proof
models, cite `sh scripts/check/check-riscv-formal-dual-track.shs` as the
aggregate SPipe evidence gate after regeneration.
Keep the generated pieces and the added proof layer divided in the SPipe manual
text: generated Lean/BYL/RTL artifacts prove regeneration shape, while manual
constraint/theorem files prove the property claim. A future regeneration must
be able to replace generated files without deleting the cited manual proof
entry point.
For flight-level or mission-critical robust-software lanes, use
`doc/07_guide/app/spipe/mission_critical_robust_sw.md` as the operator-facing
gate contract before accepting release or hardening evidence.
For SimpleOS mission-critical RISC-V evidence, also cite
`sh scripts/check/check-riscv-rtl-sby-proof.shs` and
`sh scripts/check/check-simpleos-mission-critical-release.shs`; release evidence
requires `release_blockers=none`. When changing the release wrapper, run
`sh scripts/check/check-simpleos-mission-critical-release.shs --self-test`. A
missing `sby`, `yosys`, or SMT solver is a blocked prerequisite state, not a
proof pass.
Starvation, fairness, race-condition, scheduler, channel, lock, or
resource-lifecycle claims require a concurrency/resource model gate or an
explicit blocker; a single interleaving test is not formal evidence. Wrapper
self-tests for process/coroutine/resource rows must strip at least one
row-backed theorem instead of only checking unrelated formal rows.
The SPipe manual and lane state must name the model scope, generated artifact,
durable theorem/constraint file, and exact command or wrapper that checked the
claim after regeneration. If any one of those is missing, report the lane as
blocked or incomplete rather than upgrading generated BYL/Lean/RTL output into
proof evidence.

For MCP/runtime-forwarding or startup-latency work, refresh both the lane state
file and `doc/07_guide/app/mcp/startup_performance.md` before handoff. Keep the
guide aligned with the current wrapper contract (native-first, probe-stamped,
no silent source fallback in production), the direct-`rt_*` guard policy, the
interface-cache/source-mtime contract, and the latest local smoke numbers from
`scripts/check/check-mcp-native-smoke.shs`.
Use `bin/simple deps fast|normal|deep <entry.spl>` and
`doc/07_guide/compiler/deps_tool.md` when a startup or tool-server change claims
dependency-closure reduction; record before/after file counts and the concrete
imports removed or localized.

Do not write boolean-wrapper assertions in new SPipe specs:
`expect(a == b).to_equal(true)`, `expect(a != b).to_equal(false)`, and similar
forms are quality-gate failures. Assert concrete values directly, or use
`to_be(true/false)` only when the boolean value itself is the unit under test.

For Simple Web/Electron renderer parity, keep the canonical wrapper documented
as `scripts/check/check-production-gui-web-renderer-parity-evidence.shs`.
Generated-GUI evidence may record explicit `text_normalization_pixels` for
fixture-scoped browser text antialiasing normalization, but must still require
matching checksums, `mismatch_count=0`, and `blur_or_tolerance=false`. Treat
Linux Metal readback as host-unavailable (`metal-requires-macos`) and require
native raw Metal readback evidence on macOS. A production renderer pass must
also forward `scripts/check/check-wm-browser-event-routing-evidence.shs` under
`production_gui_web_renderer_parity_event_routing_*` and require focus, window
move/maximize, title-command keyboard input, body text input, pointer down/up,
`performance.now()` availability with a positive delta, at least two
`requestAnimationFrame` ticks, CSS animation application, and
`blur_or_tolerance=false`; render/capture parity without interaction delivery
and browser timing/animation proof is incomplete evidence.
For GUI/web queue proof, runtime queue/drain receipts are necessary but not
sufficient. Production proof requires same-frame backend `device_readback`, a
positive backend handle, and matching checksum; runtime-only, synthetic-handle,
upload-only, or CPU-mirror evidence fails.

Before marking a feature tracking row `status=done`, fill `requirement`,
`research`, `plan`, `architecture`, `design`, `system_spec`, `spec_doc`,
`implementation`, `unit_tests`, `integration_tests`, and `guide`, then run
`<runtime> lint doc/08_tracking/feature/feature_db.sdn`.

When a workflow or tool contract changes, update the matching `doc/07_guide`,
`doc/06_spec`, `.codex/skills/`, `.agents/skills/`, `.claude/skills/`,
`.claude/agents/spipe/`, and `.gemini/commands/` instructions before handoff. Treat stale process docs
as unfinished work, not release cleanup.

For broad SPipe planning lanes, split independent research or implementation
checks across lower-model parallel agents when available (for example Codex
Spark, Claude Haiku, or Claude Sonnet). The best available
normal/highest-capability model must review and accept the merged result before
requirements, done marks, broad exclusions, or release-blocking verification are
trusted. Before lower-model sidecars fan out, that best-model pass must define
shared interface names, manual-facing `step("...")` flow helpers, and
setup/checker helper names; temporary helpers must fail explicitly with
`assert(false)` or `fail(...)`.
Final verification must prove the recorded cooperative review plan is complete
or explicitly `N/A`, including generated-manual quality and done-mark review.

If other Codex, Claude, or Gemini sessions are active, identify the lane this
`/sp_dev` invocation owns before editing or syncing. Do not absorb unrelated
dirty files into the feature just because they are present in the shared
checkout. Preserve other-agent work, report it separately, and commit only the
intentional lane unless the user requests a combined integration.

For scenario-oriented work, the SPipe loop also includes generated manual
review. After SSpec `.spl` scenarios are written or changed, generate the
mirrored `doc/06_spec/...` document and read it as a scenario manual. Update
`step("...")` text, capture policy, inline/previous scenario expansion, and manual
visibility until the generated manual is good enough to use without opening the
source test. See `doc/07_guide/infra/sspec_scenario_manual.md`.

Run `sh scripts/setup/install-spipe-dev-command.shs --check` on Unix-like hosts, or
`powershell -ExecutionPolicy Bypass -File scripts\install-spipe-dev-command.ps1 --check`
on Windows, to verify that this repository still routes Codex development
through `/sp_dev` and does not carry a separate `/dev` skill.

Before handoff, run the generated-spec layout guard:

```sh
find doc/06_spec -name '*_spec.spl' | wc -l
```

The result must be `0`; executable SSpec belongs under `test/`, while
`doc/06_spec` contains generated/manual Markdown and evidence assets only.
Also run `sh scripts/audit/direct-env-runtime-guard.shs --working` and
`sh scripts/audit/direct-env-runtime-guard.shs --staged` before final verify so
new app/gc env reads and process calls use env/process facades instead of local
`rt_env_get`, `rt_process_run`, `rt_process_run_timeout`,
`rt_process_spawn_async`, `rt_process_wait`, `rt_process_is_running`, or
`rt_process_is_alive`, or `rt_process_kill`.

## LLM Fine-Tune Handoff

For SPipe LLM-backed app/server work, use the fine-tune registry commands under
`.spipe/llm-finetune-process/`. If an artifact exists but misses its target eval,
record the failed eval, create or link the retry attempt, and file remaining
retry/verification/safety/deployment work in `doc/08_tracking/todo/todo_db.sdn`
and `doc/08_tracking/feature/` before reporting the handoff state.

## Reference: SimpleOS LLVM/Clang toolchain

Building a C/C++ "hello world" for SimpleOS with clang? The LLVM→SimpleOS port
is already built (easy to lose): cross clang/lld at
`build/os/llvm/cross-x86_64-unknown-simpleos/bin/`, source at
`/home/ormastes/llvm-project`, sysroot at `build/os/sysroot/`. Compile+link
works; in-guest exec is blocked. Full guide + verified commands:
`doc/07_guide/os/simpleos_llvm_toolchain.md`.
