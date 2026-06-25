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
Windows and Linux claims until platform-specific runbooks validate the same
evidence keys and RDOC gate contract.

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
for runtime-adjacent lanes and treat any new raw env/process/runtime access
outside owner modules as a fix-before-done issue.

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
native raw Metal readback evidence on macOS.
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
