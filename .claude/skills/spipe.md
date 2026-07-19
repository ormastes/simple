---
name: spipe
description: SPipe Skill — runner/docgen/process around executable SSpec `.spl` scenarios. Step-based SSpec test writing, matchers, file structure, and doc generation. Use when writing or editing `*_spec.spl` test files, debugging matcher failures, or scaffolding from `.claude/templates/spipe_template.spl`.
---

# SPipe — SSpec Runner and Docgen Process

SPipe is the process layer. SSpec is the executable `.spl` scenario authoring
surface. New manuals should be written as step-based SSpec scenarios and run or
mirrored through SPipe.

> **Modern SSpec** = a spec written *manual-first* so docgen produces a
> professional scenario manual, not a test log: user-voice `"""..."""`
> docstrings, outcome-named `it` blocks, imperative `step("...")` calls,
> capture evidence, `@manual_section` grouping, and `@req` traceability. A terse
> spec still generates a correct skeleton (screens + steps) but no explanations —
> the generator assembles, it never invents prose. Do NOT ship the anti-patterns
> in `doc/07_guide/infra/sspec_antipatterns.md`.

> **Run specs on the pure-Simple self-hosted binary, not the Rust seed.** The
> SPipe runner, docgen, and every `bin/simple test`/`run` invocation default to
> the self-hosted `bin/release/<triple>/simple` (built via bootstrap), not
> `src/compiler_rust/target/bootstrap/simple` (bootstrap-only). If a spec is
> slow or flaky because of a self-hosted compiler perf/robustness bug, fix it in
> pure-Simple (`src/compiler`/`src/lib`/`src/app`) and re-deploy, or file a
> bug/feature request — don't switch the runner back to the seed. See
> `.claude/rules/bootstrap.md` § "Default tooling runs on pure-Simple".

For installed UI/GUI/TUI CLI evidence, drive the production command (for
example `simple ui gui` or `simple ui tui_web`) and bind the receipt to the
resolved compiled sibling artifact path and digest. Running a raw
`backend_entry_*.spl` file or checking source strings proves only routing
intent, not the deployed product. Static review may accept code and evidence
contracts, but completion still requires the fresh pure-Simple live gate and
any required external GUI evidence. When the self-hosted retry cap is reached,
record the lane as blocked and stop; never substitute the Rust seed or reuse a
stale PASS artifact.

> **Interpreter-mode verification caveat.** `it` bodies may execute, but the
> outer file summary can still print `PASS`/exit 0 after matcher failures. A
> focused `interpret_file` execution must reuse
> `build_interpreter_result_wrapper` so the same compilation unit inspects
> `get_executed_test_count` and `get_exit_code`; `CompileResult.Success` alone
> is never PASS. Calibrate with deliberate-red and zero-executed fixtures, and
> keep interpreter evidence diagnostic. Tracked:
> `doc/08_tracking/bug/test_runner_interpreter_file_summary_greenwash_2026-07-03.md`.
> Reuse the pure test runner or `src/app/test/font_evidence_runner.spl`; do not
> create another result wrapper.

The SPipe dev entrypoint lives at:

**[.claude/agents/spipe/dev.md](../agents/spipe/dev.md)**

Codex routes SPipe development work through `$sp_dev`:

**[.codex/skills/sp_dev/SKILL.md](../../.codex/skills/sp_dev/SKILL.md)**

For broad SPipe lanes, split independent checks across lower-model sidecars
when available (Codex Spark, Claude Haiku, or Claude Sonnet), then require a
normal/highest-capability review before accepting done marks, broad exclusions,
or release-blocking verification. The first architecture pass defines shared
interface names, manual `step("...")` flow helper names, and setup/checker
helper names; placeholder helpers must fail explicitly (`assert(false)` or
`fail(...)`).

Before accepting done, enumerate every required host/capability row. Each row
needs fresh native PASS evidence or an explicit linked TODO and plan naming the
owner, missing prerequisite, exact resume command, and retained artifacts;
otherwise it remains active or blocked. Postponement is not completion and
cannot cover a capability executable on the current host. Preserve the affected
acceptance-criterion IDs: a postponed row stays out of exclusions, keeps its
TODO open, and blocks any phase, verify report, or goal whose acceptance depends
on it until resumed and proved.

For cross-host or native-only matrices, keep every unavailable row visible in
executable and generated-manual evidence as `unsupported` or `blocked`; never
omit it, convert it to `skip()`, or count it as PASS. A run may report
`current-host scope complete`, but the umbrella feature, SPipe phase, verify
report, and goal remain incomplete while a required row lacks fresh native
evidence. Deferral is valid only while the linked TODO remains open and its
resume plan records the host/capability, prerequisites, exact command, retained
artifacts, owner, and final reviewer.

For QEMU timing evidence, derive native applicability from the retained,
validated argv that was actually executed, and bind that exact argv to the same
serial artifact as the timing samples. Cached evidence must fail if its argv or
applicability is relabeled. Matching host and guest ISAs alone do not prove
native execution: require an explicit available KVM, HVF, or WHPX accelerator;
classify explicit TCG as correctness-only even on the same ISA. Keep mapping,
negotiation, and completion receipts ordered and correlated, and do not promote
a single timing sample to warm p95 evidence.

Final verification must fail stale workflow/tooling documentation instead of
deferring cleanup to release. If a lane changed workflow, evidence wrappers,
generated-manual shape, or verification contracts, refresh the matching
`doc/07_guide`, `doc/06_spec`, `.codex/skills`, `.agents/skills`,
`.claude/skills`, `.claude/agents/spipe`, and `.gemini/commands` instructions
before accepting PASS.

For SPipe dev lanes that produce requirement option docs, selected options must
be resolved before completion: write the final feature and NFR requirement docs,
delete the unchosen `*_options.md` files, and update the matching
`doc/07_guide` page. Do not accept a verify PASS while "Pending Selection"
option docs remain for the active feature slug.

Do not mark a goal, SPipe phase, verify report, or ship lane complete when
workflow/tooling behavior changed but the matching guide, skill, agent,
command, or generated/manual spec docs are stale. The documentation freshness
gate is part of completion, not a release follow-up.

For formal-verification evidence, generated Lean/BYL artifacts must stay
separate from manual theorem or constraint files. A SPipe scenario, generated
manual, or hardening report may cite generated artifacts only when it also names
the stable manual proof entry point and the post-regeneration gate that checked
it (`lake build`, `simple gen-lean verify`, or `simple verify check`). Treat
generated-only Lean/BYL citations as stale evidence whenever a manual proof
layer exists; update the generated contract and manual proof layer together
before accepting regeneration-safe PASS. For RISC-V evidence that spans
generated RTL sidecars plus Lean/BYL, cite
`sh scripts/check/check-riscv-formal-dual-track.shs` so SPipe evidence covers
the sidecar self-test, normal sidecar contract, and manual proof gate together.
BYL is a backend/interchange surface, not the proof result. It is helpful when
SPipe needs cheap regenerated facts, but added proof intent belongs in the
manual Lean theorem or constraint file and the generated contract must name any
BYL export consumed by that manual layer.
Mission-critical SimpleOS release SPipe evidence must also cite
`sh scripts/check/check-simpleos-mission-critical-release.shs` and keep
`release_blockers=none`; matrix readiness alone is not release evidence.
Every release-bound SPipe lane must also pass
`bin/simple test test --whole --mode=interpreter`, which combines all
spec/long-test discovery with `.spl` comment doctests and configured Markdown
code-fence tests. `--all` or `--only-slow` alone is not whole-release evidence.
If the hardening matrix reports `reason=stale-static-reports`, refresh the
named reports until `simpleos_hardening_stale_reports=none` before accepting
the lane.
SimpleOS compiler-in-filesystem lanes must prove install-image deployment and
in-guest execution. The target-native Simple payload must be embedded in the
SimpleOS filesystem under `/usr/bin/simple(.smf)`, `/bin/simple(.smf)`,
`/sys/apps/simple(.smf)`, `/sys/apps/simple_compiler(.smf)`,
`/sys/apps/simple_interpreter(.smf)`, `/sys/apps/simple_loader(.smf)`, and
`/SYS/SIMPLETOOL.SDN`. Host `bin/simple`, placeholder marker apps, host-side
compile/run evidence, or QEMU fixed-command SSH responses are not PASS evidence.
Require a QEMU or physical-board transcript that runs `/usr/bin/simple
--version` and compiles/runs a small `hello world` from the mounted SimpleOS
filesystem. For physical-board claims, also record board identity,
download/boot path, and serial or SSH transcript; otherwise classify the lane as
QEMU-only or source-present.
Ground truth (2026-07-14): cross-build + boot + FS-exec *staging* of the
target-native Simple compiler is proven on all three simpleos arches
(`bin/release/<arch>-unknown-simpleos/simple`, 4 MB static EXEC, fail-closed
`readelf` gate). In-guest *interpreter execution* is now PROVEN on x86_64 under
real OVMF (`fe9fbd8c2285`): `ssh root@guest /usr/bin/simple /hello.spl` prints
"hello from simple on simpleos" — gate `scripts/os/ssh_simple_hello_uefi.shs`
rung L4b PASS, rc=0, an ARBITRARY program (not a fixed-command fixture). Root of
the last blocker: the guest lexer's `src[start:pos].join("")` (native value-type
array-slice + join) returns `""` in the guest, so every identifier token came out
empty and nothing resolved — fixed with a char-index loop. **Lesson: native array
`[s:e]` slice + `.join()` is unreliable in guest-run code; use index loops.** The
interpreter goal was reached via the focused `simpleos_tool` payload built with
`src/compiler_rust/target/bootstrap/simple` — the deployed *full CLI* still has
separate blockers (stale two-argument `rt_env_set` artifact ABI
(`doc/08_tracking/bug/deployed_selfhost_env_set_miscompile_segv_2026-07-14.md`)
and the #99 seed-cranelift enum miscompile). So: build the payload with
`src/compiler_rust/target/bootstrap/simple` (the deployed `bin/simple` SEGVs on
every `native-build`), and classify a compiler-in-filesystem lane as
staging-proven (not in-guest-run) until the self-hosted redeploy lands. Do NOT
mark such a lane PASS on staging alone.
Starvation, fairness, race-condition, scheduler, channel, lock, or
resource-lifecycle claims require a concurrency/resource model gate or an
explicit blocker; a single interleaving test is not formal evidence.
For flight-level or mission-critical robust-software lanes, use
`doc/07_guide/app/spipe/mission_critical_robust_sw.md` as the operator-facing
contract before claiming Simple compiler, SimpleOS baremetal, NVMe firmware, or
thread/process/coroutine hardening evidence.

Check or install that wiring with:

```bash
sh scripts/setup/install-spipe-dev-command.shs --check
sh scripts/setup/install-spipe-dev-command.shs --apply
```

## Quick references in the same directory

- [`.claude/agents/spipe/research.md`](../agents/spipe/research.md) — SPipe research phase
- [`.claude/agents/spipe/spec.md`](../agents/spipe/spec.md) — SPipe spec phase
- [`.claude/agents/spipe/implement.md`](../agents/spipe/implement.md) — SPipe implementation phase
- [`.claude/agents/spipe/verify.md`](../agents/spipe/verify.md) — SPipe verification phase
- [`.claude/skills/lib/spipe_phases.md`](lib/spipe_phases.md) — phase map
- [`.claude/skills/lib/spipe_diagrams.md`](lib/spipe_diagrams.md) — diagram & concision rules (≤30 lines + ≥1 SDN diagram)
- [`.claude/skills/lib/spipe_ui.md`](lib/spipe_ui.md) — **UI skill**: the 3 main GUI check apps + framebuffer capture/verify & backend-parity gates
- [`doc/07_guide/app/spipe/mission_critical_robust_sw.md`](../../doc/07_guide/app/spipe/mission_critical_robust_sw.md) — flight-level / mission-critical robust-software gate contract
- [`doc/07_guide/infra/sspec_scenario_manual.md`](../../doc/07_guide/infra/sspec_scenario_manual.md) — SSpec scenario manual, capture, inline/previous scenario, and environmental-test guidance
- [`doc/07_guide/platform/simpleos/qemu_system_tests.md`](../../doc/07_guide/platform/simpleos/qemu_system_tests.md) — **System tests over QEMU**: per-arch live-boot SSpec specs (`test/03_system/os/qemu/`), `qemu_systest_contract.spl` descriptors, pass/missing-media/boot-fail classification (fail-closed, never `skip()`), and `scripts/check/qemu-storage-audit.shs`
- [`doc/07_guide/platform/simpleos/simpleos_baremetal_board_support.md`](../../doc/07_guide/platform/simpleos/simpleos_baremetal_board_support.md) — SimpleOS board support and the Simple compiler install-image/filesystem contract

## Scenario Manual Quality

SSpec scenarios are executable `.spl` tests. SPipe runs those tests and
generates the mirrored manuals. For user-facing, operator-facing, MCP/tooling,
UI, protocol, hardware, system, and environmental tests, generated
`doc/06_spec/...` must read like a scenario manual:

- primary flows visible as ordered `step("...")` calls;
- `@inline` setup hidden as standalone content and expanded through `@prev` or
  `@include`;
- capture evidence attached under the step that caused it;
- advanced/edge/matrix/stress details folded or skipped by policy;
- executable SSpec folded below the manual.

Run `bin/simple spipe-docgen <spec> --output doc/06_spec --no-index` and
revise the spec until the generated manual is usable without opening the source
and reports `0 stubs`.

**Never ship these anti-patterns** (full guide with real file:line evidence and
BAD→GOOD fixes: [`doc/07_guide/infra/sspec_antipatterns.md`](../../doc/07_guide/infra/sspec_antipatterns.md);
target output + worked specs:
[`doc/07_guide/app/spipe/scenario_manual_example.md`](../../doc/07_guide/app/spipe/scenario_manual_example.md)
and [`manual_examples/`](../../doc/07_guide/app/spipe/manual_examples/)):

1. Test-speak scenario names (`it "test 1"`) — name the user-observable outcome.
2. Assert-only bodies with zero `step()` — the manual renders one word.
3. Placeholder docstrings ("Comprehensive branch coverage…") — say what/why/who.
4. Magic numerics with no domain meaning (`verify(sum == 435)`).
5. Zero captures in user-facing specs — no TUI/CLI evidence blocks.
6. Fake system narrative — "end-to-end workflow" that is string/array math.
7. Flat scenario dumps — no `@manual_section` folding of edge cases.
8. Boilerplate repeated inline instead of a named `@step` helper.
9. No troubleshooting / verification appendix metadata.
10. Copy-paste "At a Glance" metadata with empty Feature IDs.
11. Internal tags leaking into user output (`(slow)` on every scenario).
12. No step vocabulary at all — neither `Given_/When_/Then_` nor `step()`.

**Capture kinds (target feature set, FR-1..FR-6 — see requirements doc):**
`tui_grid`, `gui_image`, `protocol_json`/`protocol_binary`, `bit_table` (8/16/32),
`statistics`, and user-defined kinds via a capture registry. Design:
[`doc/05_design/sspec_capture_extension.md`](../../doc/05_design/sspec_capture_extension.md);
impl plan: [`doc/03_plan/sspec_modernization_plan.md`](../../doc/03_plan/sspec_modernization_plan.md);
authoritative feature set today:
[`doc/02_requirements/feature/sspec_scenario_manual.md`](../../doc/02_requirements/feature/sspec_scenario_manual.md).

## Test API Imports

Use `std.spec.*` as the canonical SSpec test-library import in new executable
specs:

```simple
use std.spec.*

describe "Feature":
    it "operator completes the primary flow":
        step("Open the feature surface")
        expect(surface.status).to_equal("ready")

        step("Submit valid input")
        expect(result.message).to_contain("saved")
```

For CLI/TUI-facing scenarios, include a real text capture so readers can inspect
what the surface looked like. Use
`test/02_integration/app/ide/ide_feature_check_integration_spec.spl` as the
current model: it records `**TUI Captures:**`, writes
`build/test-artifacts/.../feature_check_tui.txt`, verifies the capture matches
the command output, and mirrors the sample under `doc/06_spec/...`.

`std.spipe` remains a compatibility alias that re-exports the same public
surface for existing specs. `Given_*`, `When_*`, and `Then_*` helpers are legacy
manual text helpers; prefer `step("...")` for new scenario manuals. Do not
create feature-specific replacements for `describe`, `it`, `expect`, `step`, or
the built-in matchers. UI, SGTTI, Draw IR, MCP, and protocol checks should add
helper functions that run inside normal SSpec `it` blocks executed by SPipe.
SGTTI must be zero-overhead in production paths. Keep SGTTI imports and capture
builders in explicit test/debug entrypoints; normal product entrypoints must not
import `std.ui_test.sgtti`, `SgttiTestDriver`, or debug-TUI capture modules. For
native entry-closure builds, SGTTI should be elided when not imported. Any spec
that introduces SGTTI evidence must include an import-boundary check proving the
normal path does not construct or poll the SGTTI surface.

For file/process/env I/O inside specs, import the existing facades from
`std.io_runtime` or `app.io.mod` (`file_read`, `file_write`, `file_exists`,
`process_run`, `env_get`, …) — do NOT declare raw `extern fn rt_*` intrinsics
in a spec. Spec/test files live outside the privileged runtime tiers
(`src/lib`, `src/runtime`, `src/compiler`), so a raw `rt_*` extern now trips the
`raw_rt_access` lint (warning). Route through a facade, e.g.
`use app.io.mod.{file_read_text, file_write}`.
The same rule applies to evidence tools and fixture helpers: minimize runtime
coupling first. Prefer an existing facade or add the smallest owner-module
facade instead of adding tool-local `rt_*` aliases, runtime-backed fixture
bypasses, direct backend field poking, or env/process shortcuts. A build-local
alias is a last-resort compatibility shim, not the default path for new
capability. Only runtime-owned lanes, or lanes with a proven runtime/codegen bug
and a focused gate, should edit the runtime boundary.

Before adding any new `rt_*` import, extern, wrapper, alias, runtime-backed
fixture bypass, or direct backend field access outside `src/runtime/**`, record
the decision in the lane state with `runtime_need`, `facade_checked`,
`chosen_path`, and `rejected_shortcuts`. The default `chosen_path` is
`reuse-facade`; if that is not enough, use `add-smallest-owner-facade` or
`fix-codegen-runtime-owner` before `runtime-owned-change`. Rejected runtime
shortcuts, especially fixture-only branches that hide real pixel mismatches,
must stay recorded so later agents do not repeat them.

Before touching runtime-adjacent code in an existing lane, read that lane's
recorded `rejected_shortcuts` first; do not retry a rejected `rt_*`, fixture
bypass, backend-poke, or generated-code workaround unless new evidence changes
the decision.

Before handoff, run `sh scripts/audit/direct-env-runtime-guard.shs --working`
for runtime-adjacent lanes and treat any new raw env/process/runtime access
outside owner modules as a fix-before-done issue.

For UI layout, border, color, style, or text-bound parity, prefer structured
Protocol-v2 Draw IR evidence with
`/api/test/draw-ir/diff?baseline=...&capability=draw_ir` or
`common.ui.draw_ir_diff` before relying on pixel-only assertions.
For GUI render-location assertions, use
`/api/test/draw-ir/layout?id=...&capability=draw_ir` or `expect_draw` to prove
the stable id, role/kind, geometry, hit rect, parent, and computed style inside
the SSpec case.

## UI-lane specs & diagnostics

`std.diag` (`src/lib/nogc_sync_mut/diag.spl`, guide
`doc/07_guide/infra/debugging/easy_debug_infra.md`) is the shared debug
primitive set (P0 of `doc/03_plan/ui/testing/ui_test_infra_plan.md`) that
UI-lane specs should instrument with rather than ad-hoc `print`:

```simple
use std.diag.{dbg_stage, dbg_deadline, dbg_deadline_clear, dbg_time_begin,
              dbg_time_end, dbg_summary, dbg_provenance, dbg_event_hop,
              dbg_force_facet, dbg_diag_reset}
```

- `dbg_stage(component, stage)` — stage tracer, ring cap 256; `dbg_deadline(label,
  budget_ms)` / `dbg_deadline_clear` — cooperative (thread-free) watchdog,
  breach dumps stage history once; `dbg_time_begin/end(label)` + `dbg_summary()`
  — aggregating timers, the quadratic-path finder; `dbg_event_hop(chain_id, hop,
  detail)` — one line per event hop; `dbg_provenance(claimed, actual, context)`
  — ALWAYS-ON anti-fakery assert (never gated).
- Gate with `SIMPLE_DIAG=all|stage,watchdog,timers,events` (read once, cached).
  Since specs run in the same process as module load, use the two test-only
  hooks instead of env: `dbg_force_facet(facet)` to force a facet on mid-spec,
  `dbg_diag_reset()` to clear all module state between `it` blocks.

**Two interpreter landmines proved during the P0 spec work** (both documented
in `diag.spl`'s header and `diag_spec.spl`'s header comment):
1. `if val Some(x) = dict.get(k):` **silently never matches** — `Dict.get()`
   returns the raw value or `nil`, NOT a `Some(..)`-tagged Option. Use
   `dict.get(k) ?? default` or `!= nil` instead.
2. Module globals mutated inside functions are **stale when read directly from
   a spec `it` block** — the interpreter snapshot the `it` block sees does not
   reflect writes made by module functions. Always assert through the module's
   own accessor functions (e.g. `dbg_last_emit()`, `dbg_timer_stats(label)`),
   never by reading a module-level `var` directly from the spec.

**UI interaction (Playwright-like `UiTest`/`locator`) is designed, not yet
implemented.** See `doc/05_design/ui/testing/ui_test_infra_design.md` (the
`UiSession`/`Locator`/`Lane` API) and `doc/03_plan/ui/testing/ui_test_infra_plan.md`
(phases P1-P6). Specs that need to click/type/snapshot a live UI should follow
that plan rather than hand-rolling a driver against `ui.test_api`/SGTTI directly.

## Rendering Checks (`expect_draw` style)

For GUI, Web, 2D, Draw IR, and WASM rendering specs, use `expect_draw`-style
helper functions inside normal SSpec `it` blocks. The helper may wrap repeated
setup/readback, but it must contain real assertions and must not replace
`expect`, `describe`, `it`, or the canonical matchers.

For GUI/web font work, reuse the canonical `FontRenderer` and assert semantic
`DrawIrComposition` text/style before backend/readback evidence. `WebIR` remains
the existing semantic/layout model; transient `FontRenderBatch` atlas/device
material belongs only to Engine2D, never WebIR or Draw IR. The canonical
Web producer uses the HTML/WebIR-to-DrawIR owner; the canonical GUI producer
uses `widget_tree_to_draw_ir`, never a private widget command collector. The
submitted payload must be that exact composition before dispatch can pass; a
separate frame event leaves dispatch `not_requested`. Preserve the executor's
exact readback source instead of replacing it with generic provenance. The
canonical WM frame route is `SharedWmScene -> DrawIrComposition -> Engine2D`;
`shared_wm_scene_render_*_to_backend` and `_to_pixel_buffer` are compatibility
renderers, not selected-font completion. Reject evidence built on an app-private
font draw path or on Engine3D HUD/world as a GUI/web/2D shortcut. A synthetic
composition is supporting evidence only: production acceptance must exercise
the real hosted frame owner, canonical SimpleOS entry wiring, and the retained
QEMU framebuffer crop, with platform backends limited to final-pixel
presentation.

Shared-font SSpec manuals freeze these exact steps: `Load the pinned multilingual
font manifest`; `Accept exact-face-bound simple-script shaping`; `Prepare one
shared font batch for 2D and 3D`; `Emit the selected font composite program and
plan compilation`; `Prove native submission and device readback`. Engine3D
HUD/world stays a separate consumer lane. Full rules live in `$sp_dev` under
“Shared multilingual font work.”
The final irreversible registered-only SimpleOS shaping scenario uses exact
validated Arabic/Devanagari registered bytes, no host font ABI or filesystem
access after the mode switch, handle-free Draw IR, and the existing
selected-byte `FontRenderer`; it never implies a QEMU framebuffer PASS.
AC-13 review rejects raw `rt_mutex_*` ownership in font modules, mutable
module-global engine pools, and hosted unsynchronized generation counters;
freestanding initialization constraints must be repaired through the existing
facades rather than by adding parallel runtime owners.
NFR-008 promotion must flow from `VulkanFontCompositeEvidence` and
`vulkan_font_stage_evidence_ready` into durable `FontPerfBudgetEvidence`, then
through `read_font_perf_evidence` and `expect_font_perf_budget`. `queue_device`
is one fused submit-through-device-completion interval; the later `sync` field
is fence observation, not disjoint device time. Offscreen rendering records
`not-applicable-offscreen` presentation and still requires device readback.
Vulkan promotion also requires the exact pinned precompiled-SPIR-V hash;
magic-valid alternative modules and runtime GLSL remain unpromoted. The checker
requires extracted optimization/font source bytes to match their emitter-declared
hashes and rejects missing or malformed hashes before compilation. A well-formed stale
Vulkan source may compile and retain `.comp`/`.spv` candidates for review, but
evidence remains invalid until both source and artifact pins match.
Portable font admission aggregates only `PORTABLE_COMPUTE_TARGETS` and first
requires emitted semantics to match `PORTABLE_COMPUTE_EXPECTED_SEMANTICS`,
`candidate_compiled=true`, and `artifact_validated=true`. Evidence records the
compiler and validator path/version/SHA-256; Vulkan additionally requires a
passing `spirv-val` row, actual loaded shader-compiler library path/SHA-256
and loader-log SHA-256 under a clean loader environment, rejection of any
operator-supplied expected-library path mismatch, and byte-identical independent
A/B SPIR-V compiles. The current proof admits only a resolved native-ELF
compiler on glibc; wrappers and other loaders fail closed, and
`glslangValidator` is diagnostic-only. Stale pins remain
`pinned_verified=false`. Independent
review may then update tracked source/artifact pins, after which a reproducing
run must set `pinned_verified=true`; never repin merely to green the first run.

For RenderDoc evidence, use the shared helper interface instead of spelling
`renderdoccmd` directly in each spec or check script:

- `scripts/tool/renderdoc-evidence.shs capture-simple` for the Simple
  in-application `rt_renderdoc_*` Vulkan Engine2D path.
- `scripts/tool/renderdoc-evidence.shs capture-html` for original RenderDoc
  Chrome HTML/CSS capture.
- `scripts/tool/renderdoc-evidence.shs capture-electron-html` for bundled
  Electron Chromium HTML/CSS capture.
- `test/helpers/renderdoc_capture_helper.shs` for test-facing shell helpers.

Record `.rdc` path, `RDOC` magic validation, capture log path, and any
host-unavailable reason as artifact captures. Screenshot-only evidence is not
Vulkan IO-level RenderDoc evidence.

For HTML-backed GUI modernization, screenshots and DOM audits are not enough
when a lane claims event handling. Require structured Electron interaction
evidence for focus, keyboard/input, pointer, and click delivery on visible
controls, or an explicit host-unavailable result. The production GUI/web
renderer parity wrapper now consumes
`scripts/check/check-wm-browser-event-routing-evidence.shs`; a green production
claim must expose `production_gui_web_renderer_parity_event_routing_*` with
focus, move, maximize, title-command, text-input, pointer-down, pointer-up, and
browser timing/animation proof: `performance_now_available=true` with a positive
`performance_now_delta_ms`, at least two animation frames,
`css_animation_probe=true`, and `blur_or_tolerance=false`.

For GUI/web/2D Vulkan comparison, use
`scripts/setup/setup-gui-web-2d-vulkan-env.shs --check` for readiness,
`--browser-backing` for focused direct Electron Chromium backing proof, `--run`
for direct Electron/Chrome/Simple launch probes, and
`--renderdoc-simple` for the Simple in-application RenderDoc debug path on a
prepared Linux or macOS RenderDoc host. Normal runs use the repo-managed
self-hosted `bin/simple` selected by the wrapper. If it is unavailable or lacks
the current RenderDoc externs, report the bootstrap/runtime gap; never substitute
the Rust seed. Use all-lane `--renderdoc` only for cross-surface
evidence collection. For Windows setup, read
`doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md`: `vulkaninfo --summary`,
DirectX availability, Chrome installation, and Electron installation are host
readiness only, not browser Vulkan proof. Vulkan SDK readiness requires a fresh
shell where `glslangValidator`, `spirv-as`, and any required shader compiler
such as `dxc` resolve; if the SDK installer is canceled at an administrator
prompt, record `sdk-tools-missing`. The Mac setup starts with Homebrew Vulkan tooling
(`vulkan-tools`, `vulkan-loader`, `vulkan-headers`, `molten-vk`,
`spirv-tools`, `glslang`) and `vulkaninfo --summary` showing the Apple GPU
through MoltenVK. That only proves host readiness. Completion evidence still
needs Simple Vulkan/Engine2D readback or RenderDoc proof, original
Chrome+RenderDoc proof, Electron+RenderDoc proof, and production GUI/web parity
proof. If Chrome or Electron renders pixels but its log says `angle=vulkan` was
not in the allowed implementations, classify the browser lane as
`vulkan-angle-unavailable`; do not treat the bitmap as Vulkan-backed proof.
Browser `RDOC_RENDERDOC_HOOK_CHILDREN=0` and Chromium `--in-process-gpu` runs
are diagnostic only unless they still emit valid browser GPU-process `.rdc`
evidence with `RDOC` magic and prove Vulkan remains active.
The aggregate audit must also expose comparison artifact status keys:
`gui_web_2d_vulkan_comparison_fixture_status`,
`gui_web_2d_vulkan_comparison_artifact_status`,
`gui_web_2d_vulkan_comparison_artifact_reason`,
`gui_web_2d_vulkan_electron_argb_viewport_match_status`,
`gui_web_2d_vulkan_electron_argb_file_status`,
`gui_web_2d_vulkan_electron_argb_nonblank_status`,
`gui_web_2d_vulkan_chrome_argb_file_status`,
`gui_web_2d_vulkan_chrome_argb_viewport_match_status`,
`gui_web_2d_vulkan_chrome_argb_nonblank_status`,
`gui_web_2d_vulkan_simple_evidence_file_status`, and
`gui_web_2d_vulkan_simple_backend_status`. The audit may still emit
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
Browser Vulkan proof must be read from
`gui_web_2d_vulkan_browser_backing_status`,
`gui_web_2d_vulkan_browser_backing_reason`, and
`gui_web_2d_vulkan_browser_backing_mode`; fallback bitmap comparison is not
Vulkan-backed browser proof, and the aggregate GUI audit must remain incomplete
until browser backing is `pass`.
Read current macOS blocker lanes from
`gui_web_2d_vulkan_renderdoc_blocker_status`,
`gui_web_2d_vulkan_renderdoc_blocker_reason`,
`gui_web_2d_vulkan_renderdoc_blocker_gate_count`, and
`gui_web_2d_vulkan_renderdoc_blocker_gates` before claiming that RenderDoc,
Simple, Electron, or Chrome Vulkan-backed capture is ready; blocker status
`blocked` is a completion blocker, not a warning.
GUI widget fixture evidence must also prove per-widget feature witnesses via
`gui_widget_rendering_fixture_coverage_renderdoc_fixture_widget_features`,
not only widget/class presence.
When the claim is that all GUI items are RenderDoc-tested, run
`scripts/check/check-gui-widget-renderdoc-goal-status.shs`; require
`gui_widget_renderdoc_goal_status=pass`,
`gui_widget_renderdoc_goal_widget_feature_covered_count=43`,
`gui_widget_renderdoc_goal_simple_gate_status=pass`,
`gui_widget_renderdoc_goal_electron_gate_status=pass`, and
`gui_widget_renderdoc_goal_blocked_gate_count=0`. Normal non-Mac runs may report
`incomplete`, but release or completion claims must use `--strict` with real
Simple Vulkan Engine2D and Electron Chromium/Vulkan `.rdc` evidence.
Defer Linux claims until platform-specific runbooks validate the same evidence
keys and RDOC gate contract.

For Tauri2 mobile renderer parity, use
`scripts/check/check-tauri-mobile-renderer-parity-evidence.shs`; it requires
desktop production GUI/Web parity first, iOS WKWebView screenshot evidence with
Metal markers, and Android WebView screenshot evidence with Vulkan/skiavk or
host-emulator Vulkan markers. It also requires the mobile MDI proof statuses
for events, capture, performance, and animation to pass. Read those from
`*_mdi_event_status`, `*_mdi_capture_status`, `*_mdi_performance_status`, and
`*_mdi_animation_status`; they are derived from the `[tauri-shell] mdi proof:`
JSON and prove event routing, viewport capture dimensions, `performance.now()`,
requestAnimationFrame, and CSS animation support. Treat `F/DEBUG`,
`Fatal signal`, `VulkanManager`, `Headless UI completed`, or subprocess parse
failures in Android logcat as hard blockers, not as Vulkan proof.
Host/emulator ANGLE/Vulkan startup logs are supporting evidence only when
`com.simple.ui` remains foreground, a `[tauri-shell] render, html_len=` marker
is present, the screenshot is captured from the live app, and the MDI proof is
valid.

Prefer the strongest available oracle for the surface:

- HTML/CSS/WASM-backed surfaces: first assert HTML, DOM-visible text,
  attributes, layout-relevant objects, or canvas/wasm bridge state.
- Draw IR and object-model surfaces: assert emitted draw commands, scene nodes,
  object state, bounds, colors, event/source metadata, or deterministic hashes.
- Native GUI/raster-only surfaces: use screenshots, goldens, framebuffer
  readback, pixel diffs, or hashes as fallback or supplemental evidence.

Do not accept placeholder rendering passes: no `pass_todo`, no
`expect(true).to_equal(true)`, no empty draw helpers, and no screenshot-only
claim when HTML, Draw IR, object state, or visible-text evidence is available.
If the host cannot execute a renderer, skip with a concrete reason or assert an
available non-raster oracle. Keep executable specs under `test/...`; generated
manual docs and evidence assets belong under `doc/06_spec/...`, and
`doc/06_spec` must never contain executable `.spl` specs.

Before final verify, run `sh scripts/audit/direct-env-runtime-guard.shs --working`
and `sh scripts/audit/direct-env-runtime-guard.shs --staged` so new app/gc env
reads and process calls use env/process facades instead of local `rt_env_get`,
`rt_process_run`, `rt_process_run_timeout`, `rt_process_spawn_async`,
`rt_process_wait`, `rt_process_is_running`, `rt_process_is_alive`, or
`rt_process_kill`.

For IDE Office Markdown/PPT rendering hardening, keep the canonical guide at
`doc/07_guide/app/ide_office_plugin_suite.md` current. Specs should prove the
Markdown GUI path uses `wysiwyg_preview_document_html` with escaped content and
CSS, while slide/PPT HTML render specs should prove escaped text, sanitized
`#RGB`/`#RRGGBB` colors, clamped geometry, and positioned slide boxes. The IDE
feature-check report must expose these markers in both TUI and GUI modes:
`css_doc=true escaped=true` for Markdown and
`ppt_html=true safe_css=true positioned=true` for slides.

### Simple Web production hardening

For Simple Web/browser production-boundary work, keep the selected Feature
Option C and NFR Option C contract current:

- final requirements live at
  `doc/02_requirements/feature/simple_web_browser_production_hardening.md` and
  `doc/02_requirements/nfr/simple_web_browser_production_hardening.md`;
- executable traces belong in `test/01_unit/app/ui/web_auth_hardening_spec.spl`,
  `test/01_unit/app/ui/ws_handler_spec.spl`,
  `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`, and
  `test/03_system/gui/wm_compare/production_gui_web_renderer_parity_hardening_spec.spl`;
- regenerate mirrored manuals with `bin/simple spipe-docgen ... --output
  doc/06_spec --no-index`, require `0 stubs`, and keep
  `find doc/06_spec -name '*_spec.spl' | wc -l` at `0`;
- canonical `/ui/ws` requires an origin-bound bearer token, legacy `/ws` returns
  `404`, and query-string bearer transport is non-authorizing even if
  `SIMPLE_UI_WEB_ALLOW_QUERY_TOKEN=1` is present;
- local Linux evidence may record deterministic `host-unavailable` rows, but
  macOS Metal, AMD ROCm/HIP, Windows DirectX, and real browser WebGPU native
  device-readback remain external-host gates until proven on those hosts.

For compiler cache, formal verification, loader, JIT, or accessor-forwarding
changes, add semantic invalidation specs. Public ABI changes, field-wrapper
changes, forwarded getter/setter changes, and generated accessor dependency
changes must miss stale interpreter, SMF, and JIT cache entries instead of
reusing old code. Keep the spec close to the cache owner and mirror it into
`doc/06_spec` as a readable scenario manual.

### Native HTTPServer benchmark evidence

For native HTTPServer/static-file performance work, use
`scripts/check/check-native-pure-simple-goal-status.shs` as the aggregate gate.
The focused peer wrappers are `check-web-server-nginx-live-compare.shs`,
`check-web-server-static-external-live-compare.shs --require-simple-ge-all`,
`check-web-server-go-erlang-static-compare.shs --require-simple-ge`,
`check-httpserver-live-static.shs`, and
`check-httpserver-static-profile-counters.shs --broad --require-retained`.
Keep `doc/07_guide/infra/testing/benchmarking.md`,
`doc/10_metrics/perf/web_server_nginx_compare.md`, and
`doc/09_report/perf/web_server_nginx_compare_2026-06-17.md` aligned when rows
or wrappers change. Current retained nginx rows are 1KB Simple `15503.65` RPS
vs nginx `15115.00`, and 1MB Simple `1884.42` RPS vs nginx `1376.25`; the
retained Vulkan offscreen 8K row is `3527` FPS.

Avoid boolean-wrapper assertions such as `expect(a == b).to_equal(true)` or
`expect(a != b).to_equal(false)`. Prefer direct value matchers such as
`to_equal`, `to_be_greater_than`, `to_contain`, or `to_be_nil`; use
`to_be(true/false)` only when the boolean itself is the behavior being tested.

### GPU-offload and effect discriminators

When a feature claims work is offloaded to the GPU (or that an effect like
transparency/blend is applied), the spec must *discriminate the claim*, not just
observe a pass:

- **Legacy font payload bridge.** The checksum-verified
  `{CUDA,ROCM,HIP,OPENCL}_{VECTOR,BITMAP}_FONT_*` environment transport proves
  only the legacy payload bridge, not direct native dispatch. Its compatibility
  spec asserts BOTH states: with NO payload → CPU fallback
  (`gpu_returned_glyphs == 0`, `cpu_fallback_hits > 0`, reason
  `production-gpu-dispatch-not-wired`); with a matching payload → GPU stats
  (`gpu_returned_glyphs == 1`, `cpu_fallback_hits == 0`). Add a corrupt-checksum
  case that must be REJECTED (falls back). If the impl reports GPU-offloaded
  regardless of payload, it is a cover-up and the compatibility spec must fail
  it. See
  `test/01_unit/lib/common/text_layout/bitmap_font_gpu_offload_spec.spl`.
- **Shared font batch native proof.** Direct 2D/3D font composition must begin
  with the same batch generation plus quad/atlas payload hash (do not infer
  face/glyph identity from fields the current compatibility batch lacks), then
  separately prove compiled
  versioned entry, nonzero device/program/texture/sampler/pipeline handles,
  true atlas/destination allocation counts with guarded indices, atlas upload
  and bind, submit/draw, completed fence, and device-origin
  readback against an absolute CPU oracle. Emitted source, environment payload,
  upload alone, software backend names, simulation, or equal checksums are not
  native proof. Record unavailable hardware as `unavailable`; never promote it.
  Before native promotion, the exact Pure Simple shaping/corpus gate must accept
  the face for the language/script; a codepoint raster/layout witness alone is
  diagnostic and leaves the matrix cell `unavailable`.
  Run shared multilingual font acceptance SSpecs with
  `SIMPLE_NO_STUB_FALLBACK=1 bin/simple test <spec> --mode=native`; interpreter runs are diagnostics and cannot
  promote a manifest cell, backend, or performance row.
  The focused `src/app/test/font_evidence_runner.spl` uses
  `preprocess_spipe_native_result_file`, not an interpreter wrapper. Invoke it
  with the admitted pure-Simple compiler path and SHA-256, the core-C runtime
  directory and archive SHA-256, then the spec path. It builds a private
  `/tmp/spipe_native_*_spec.spl`, hashes and rechecks the wrapper/providers,
  executes the native artifact, and admits only an exact summary plus one
  `test-runner: native result wrapper complete` marker. Require exit 1 plus the
  exact `error: test-runner: spec failed` suffix for deliberate-red and exit 1
  plus `test-runner: no examples executed` without a completion marker for
  zero-executed; reject 2/124/132/139. Use
  `scripts/check/fixtures/font_evidence_runner_fail_spec.spl` and
  `scripts/check/fixtures/font_evidence_runner_empty_spec.spl`. It must use the
  atomic exclusive wrapper creation, map every non-success build nonzero, and
  delete its wrapper and native binary. Retain exact commands, runner binary SHA-256,
  and both logs under the canonical `$system_test` artifact path.
  Its generated `fail(...)` helper records the failed assertion and immediately
  exits 1; it must never fall through into a nil/default return and turn a test
  failure into SIGILL. Source-defined replacements for `fail` remain rejected.
  Resolve matrix policy by exact language and category. Unknown axes fail
  closed, and `witness_family` must not be treated as a loadable asset unless
  the resolved status is `native` or `fallback`.
  Supplementary-plane/emoji claims must exercise a real format-12 cmap witness
  (currently `U+1F600`) and prove the selected run face owns the returned glyph
  ID; parser-only lookup is not fallback acceptance.
  Shaped-run rendering must fail closed unless the `OtFont` is explicitly bound
  to the same live runtime face generation, blob/runtime cmap glyph IDs agree
  for every codepoint, and cache/atlas identity includes face + generation +
  glyph index + size. A codepoint used as a fabricated glyph index or a stale
  freed handle is a hard failure. Engines consume the neutral text-layout run
  and `FontRenderBatch`, never the Skia shaper type directly.
  Preserve absolute source index and cluster identity inside each shaped glyph
  before any reversal/reorder; language/script/direction and current advance/
  offset metadata must stay aligned with glyph order. Cmap parity is direct
  material evidence only: complex scripts and multi-codepoint emoji sequences
  remain invalid while substitution/positioning completeness is false.
  Engine3D neutral HUD/world acceptance is CPU compatibility evidence only:
  world text projects one anchor into a screen-space billboard. It does not
  prove native texture upload, depth/occlusion, pipeline draw, fence, or
  device-origin readback.
  Distinguish GPU atlas composition from CPU glyph rasterization and from direct
  GPU outline rasterization.
  The OpenCL adapter must additionally prove the versioned shared source,
  generation-keyed atlas upload with load/unload invalidation, checked dirty-row
  offsets after the initial full upload, full upload on reset/gap/invalid dirty
  metadata, exact 0..14
  argument binding, submit/synchronize, and `device_readback`; conditional unit
  execution is not a release PASS when the device is unavailable.
  The CUDA adapter must prove the separately source-tracked Simple-generated
  PTX companion passes runtime PTX-hash, entry, and program-version checks,
  while checker/SPipe exact equality binds its pinned source and emitter-version
  hashes to the current Simple emission and
  the default 2D module provides no font entry; all 15 value/pointer slots are ordered exactly,
  atlas generation is invalidated on font replacement, each accepted prefix is synchronized before
  CPU-mirror parity is updated, and final pixels come from `device_readback`.
  Production loading additionally requires packaged or tracked Simple-generated
  PTX bound to an immutable trusted hash and program version; ignored `build/`
  output and caller-provided adjacent hashes are not trust anchors.
  The Metal adapter must prove compiler/runtime source equality, the optional
  native pipeline, exact 13-word/52-byte ABI, native-only typed routing (never
  `metal-on-vulkan`), completed prefix dispatch, and device-origin readback.
- **CLDR ranking replay.** A release top-language claim requires pinned
  `common/supplemental/{supplementalData,supplementalMetadata,likelySubtags}.xml`
  from the selected CLDR object, verified source hashes, two byte-identical
  `cldr_rank_languages` generations, and exact top-10 plus rank-11 comparison.
  Compare every language total and script subtotal with the checked-in derived
  ledger. The synthetic unit fixture proves scanner/arithmetic behavior only.
- **Effect oracles are absolute, not "non-zero".** Transparency/blend specs use
  effective alpha `sa=(coverage*fg_a+127)/255`; when `sa==0`, output is the
  unchanged background. Otherwise assert
  `dst_weight=bg_a*(255-sa)/255`, `out_a=sa+dst_weight`, and
  `out_rgb=(fg_rgb*sa+bg_rgb*dst_weight)/out_a`.
  Full coverage replaces the foreground only when `fg_a==255`. See
  `font_glyph_transparency_spec.spl`.
- **Config/env backend selection.** When one API selects its lane (SIMD CPU vs
  GPU) by environment (`SIMPLE_2D_BACKEND`), assert the override is honored when
  the backend initializes AND ignored (auto-probe, value changes) when it cannot —
  never just that some backend is returned. See
  `engine2d_env_backend_select_spec.spl`.
- **ExecTarget (std.compute) two-level + suggest/require.** The compute stdlib
  (`src/lib/nogc_async_mut/compute/`, guide
  `doc/07_guide/lib/compute/exec_target_compute_stdlib.md`) tags a device CLASS
  (`default/cpu/simd_cpu/gpu/fpga/simd`) and auto-resolves the BACKEND. Specs must
  prove BOTH enforcement modes: `suggest` falls back to the best available
  (`resolved=true`), `require` of an absent class/backend fails closed
  (`resolved=false` → caller `rt_exit 70`) — never a silent downgrade. Dispatch
  honesty is payload-gated like font offload: a device target with NO payload runs
  the CPU reference (`ran_on_cpu=true`, no masquerade); the value must equal the CPU
  oracle in both branches. Avoid generic `!=`/2-arg `==` on `[T]` in comparators
  (interp bug; use `less` + derive equality).
- **Per-backend kernel EMISSION (no GPU needed).** Verify only targets the
  emitter actually supports: CUDA `__global__ void`, OpenCL `__kernel void`,
  Metal `kernel void` + `[[thread_position_in_grid]]`, and WebGPU
  `@compute @workgroup_size`. Vulkan requires validated SPIR-V evidence, not a
  fabricated text marker. See `gpu_compute_algorithm_kernels_spec.spl`.
  When font composition accompanies a generated optimization module, require a
  separate font artifact/compile plan, a distinct `_font_atlas` path, and the
  versioned font entry in exported-symbol evidence. Never concatenate WGSL
  modules whose storage/uniform bindings overlap.

### GPU / drawing / event honest backend baseline (2026-07-06)

Before writing GPU-processing, 2D-drawing, or event specs, read the intensive
test plan `doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md` (+ `_tldr`)
and the coverage guide `doc/07_guide/testing/gpu_rendering_tests_gap_analysis.md`.
The plan is: **shared portable bodies (Linux CI) + system-specific device
checkpoints** across processing {vulkan, metal, cuda, hip} × drawing {metal,
vulkan, directx}, with `read_pixels()`→PPM as the absolute oracle. Honest state a
spec must not paper over:
- GPU compute (`std.compute`/ExecTarget) is a **payload-gated simulation** — it
  reports GPU provenance but runs a CPU reference; real device execution is proven
  only on Metal. Assert value == CPU oracle in BOTH branches + the provenance flag.
- **Vulkan** `line`/`circle_outline`/`rounded_rect` dispatch a validated EMPTY
  shader (zero pixels); **Metal** `clip` is a no-op; **cpu_simd** is an honest
  alias of `cpu` (no live SIMD). A drawing spec must catch these, not match a
  same-code-path tautology.
- The GPU job/event scheduler (`host_gpu_event_queue.spl`,
  `draw_ir_runtime_queue.spl`) is real (EMPTY→QUEUED→SUBMITTED→COMPLETED); the
  debug-log feature instruments it with `std.diag` (`dbg_event_hop`/`dbg_stage`/
  `dbg_provenance`, `SIMPLE_DIAG=events,stage`) — never re-introduce a fabricated
  `estimated_ms` speedup.
- HTML/CSS Draw-IR boxes now render borders/gradients/radius/shadow (not flat
  fill); `<img>` remains blocked (`engine2d_draw_ir_image_path_no_resolver_2026-07-06`).

### Backend isolation in UI specs (2026-07-06)

Specs for **app-level** UI behavior must drive a **facade**, never a backend or
`rt_*` extern directly — the spec exercises the same isolated path the app ships:

- 2D: `Engine2D.create_requested_backend(w,h,name)`; HTML→pixels:
  `web_render_backend(name,w,h).render_html_to_pixels(html)` (`name` =
  `pure_simple`|`chromium`); windows/sessions: `GuiRenderer` once it lands
  (P3 Gap A). Never construct `MetalBackend`/`SoftwareBackend`… or call
  `simple_web_engine2d_render_html_pixels`/`simple_web_layout_render_html_*`
  from a spec that stands in for app code.
- Parity/readback specs assert **provenance**, not just pixels — check the
  `ReadbackSource`/backend name the facade reports (e.g. metal vs software) so a
  silent software fallback (MEMORY 06-10) fails the spec instead of green-washing.
  Equality-to-CPU-oracle alone is a same-path tautology; see § "Equality is not
  correctness".
- Backend-engine or `rt_*` calls belong only in `src/lib/**/gpu/**` and the
  designated `io`/`ffi` facades. A spec that must touch those directly is a
  backend/library spec, not an app spec — place it accordingly.
- Full rules, allowlist, per-lane call patterns, and the source-contract gate:
  [`doc/07_guide/ui/rendering/backend_isolation_guide.md`](../../doc/07_guide/ui/rendering/backend_isolation_guide.md).

## Startup-Sensitive Specs

If a SPipe change touches `simple run`, direct file argv parsing,
`get_cli_args`, `std.cli`, `.shs` dispatch, mmap/read-ahead startup loading,
launch metadata, or startup dynlib policy, keep this executable integration
spec in the evidence set:

```text
test/02_integration/app/startup_argparse_mmap_perf_spec.spl
doc/06_spec/02_integration/app/startup_argparse_mmap_perf_spec.md
```

Do not move executable startup specs into `doc/06_spec`, and do not route
script startup through compile/JIT as a workaround for a failing fast path. Fix
the fast path or record a concrete bug.

For MCP/LSP/tool-server startup work, follow the startup-reduction ladder in
`doc/07_guide/app/mcp/startup_performance.md` (tldr alongside): measure direct
vs through-the-wrapper first (a ~2× gap means the wrapper duplicates work,
e.g. a probe handshake), then remove work in order — no double start, exec
compiled artifacts, lazy tool registry, SHB interface-only loading, thin
host-wrapper imports — before moving work (background compile, keep-warm).
Startup gates bound startup only; MCP stdio reads must never gain timeouts.
For Stage 4 full-CLI acceptance, run the bounded
`scripts/check/check-bootstrap-essential-tools-smoke.shs` once after candidate
admission and before later bootstrap/deploy work. Point it at the exact fresh
CLI, disable stub fallback, and require calibrated test-runner, lint, and
duplicate-check outcomes plus the aggregate pass marker. Raw source, a deployed
wrapper, Rust seed, or stale binary is not evidence. This sanity does not
replace release `--whole` or repository-wide policy checks, and it must not be
copied into compiler Stages 2 or 3.
During repair of a crashing stale pure-Simple runner, the Rust bootstrap may
run test evidence only through explicit `SIMPLE_TEST_RUNNER_RUST=1`, the
canonical resource cap, `timeout -k`, and redirected output. This is temporary
repair evidence, never a production fallback or release PASS; remove it once
the rebuilt pure runner passes the same fixture.
For bootstrap MCP acceptance, run the shared bounded checker once after both
Stage 5 outputs exist and before deploy. Point it at the exact fresh MCP/LSP
paths, disable fallback, send initialize/initialized/tools-list, and require
successful semantic `simple_status` and `lsp_symbols` results. Missing or stale
artifacts, crashes, timeouts, malformed/error responses, and nonzero exits fail
closed. Do not copy this gate into compiler Stages 2 through 4; `--no-mcp`
makes no MCP health claim. See
`doc/07_guide/tooling/mcp_handshake_regression.md`.

### dynSMF Background Compile Startup

If a task mentions compiling SMF while the interpreter reads/runs scripts,
precompiled dynSMF artifacts, GUI-library SMF loading, or `build/dynsmf/*.smf`,
start from the general dynSMF lane:

- implementation: `src/os/smf/dynsmf_session.spl`
- startup adapter: `src/app/startup/dynsmf_autoload.spl`
- canonical wrapper: `scripts/check/check-low-dependency-dynsmf-build-plans.shs`
- unit spec: `test/01_unit/os/smf/dynsmf_session_spec.spl`
- startup integration spec: `test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl`
- guide: `doc/07_guide/lib/api/dynlib_api.md`

Do not treat this as a GUI-only feature. GUI renderer artifacts are consumers of
the same manifest/build-plan/background-compile evidence contract used by
non-GUI entries such as `file_io` and `net_io`. Startup may record
`compile_background` queued evidence while continuing interpreter execution, but
checked autoload must remain fail-closed until a valid `SMF\0` artifact exists.

## Equality is not correctness (false-green guard)

A parity/equality assertion (`expect(a).to_equal(b)`, "backend A matches backend
B", "output == reference") passes whenever both sides are equal — **including
when both are empty, both are wrong in the same way, or both come from the same
code path.** Equality alone never proves the values are *right*.

When the two sides share the code you just changed, or one side can silently fall
back to mirroring the other, pair the equality check with an **absolute oracle**:

- a known fixed point with a known value (filled shape center == draw color; a
  far/background pixel == background; a counter == an independently computed total);
- proof the producer actually ran (e.g. a GPU `gpu_frame_complete`/hit-counter
  flag, not just "no error"), so a no-op fallback can't pass as success;
- two *independently produced* artifacts, never one value compared to itself.

This area of the codebase has a documented false-green history (software-vs-itself
"GPU parity", scalar paths reporting `has_neon` without running NEON, all-black
buffers matching all-black, and **hard-coded captured-browser pixel tables pasted
over the renderer output** — memorizing the reference instead of rendering it,
which silently goes stale and is machine/version-specific). See
`doc/07_guide/ui/engine2d_cpu_metal_bit_parity.md` ("MATCH ≠ correct"). When a
real renderer genuinely cannot bit-match a reference (e.g. software text AA vs a
browser font rasterizer), do **not** memorize pixels — render honestly and mark
the case known-divergent (the web-layout manifest's `policy=track-text-divergence`
classifies such cases as *tracked*, not *exact* or *fail*). When the
test runner can't execute the `it` blocks (e.g. it segfaults importing a heavy
module graph), run the same assertions through a `bin/simple run …` harness and
keep the absolute oracle in it — don't downgrade to "files load".

## GUI sanity tests (pure-Simple lane)

After any GUI / engine2d / web-render change, sanity-check the **three main GUI
check apps** (one per surface; on macOS the lane = Engine2D CPU/NEON + Metal):

1. **2D rendering** — `examples/06_io/ui/engine2d_shapes_gui.spl` (primitives;
   backend variants `engine2d_cpu_simd_gui.spl` / `engine2d_metal_gui.spl`).
2. **GUI widgets** — `examples/06_io/ui/widget_showcase_gui.spl` (full widget catalog).
3. **HTML rendering** — `examples/06_io/ui/web_render_file_gui.spl <file.html>`
   (real HTML+CSS → web layout → Engine2D; headless PPM via `web_render_page_ppm.spl`).

Launch (macOS): `scripts/gui/macos-gui-run.shs <app.spl>`. **Verify the
framebuffer, not the screenshot** (`read_pixels()` → P6 PPM is the absolute
oracle; region screen-capture is flaky). Full launch/capture/parity-gate details:
**[`lib/spipe_ui.md`](lib/spipe_ui.md)** (the UI skill). Reference:
`doc/04_architecture/ui/simple_gui_stack.md` → "GUI Sanity Apps". The web-layout
lane is interpreter-bound (~1.5 ms/px) — keep web sanity surfaces ≤ ~900×760.

## Template

```
cp .claude/templates/spipe_template.spl test/my_spec.spl
```

## FILE.md Enforcement

SPipe verify runs `sh scripts/check-workspace-root-guard.shs audit --strict`.
Default: diagnose and report. Auto-fix: trace origin and fix creating code.
See [`doc/07_guide/infra/workspace/file_manifest_tldr.md`](../../doc/07_guide/infra/workspace/file_manifest_tldr.md).

## Code Quality Checks

SPipe verify and implementation phases enforce these quality gates:

- **Duplication**: no line-level, token-level, or semantic duplicates; parameter
  lists with 3+ fields become a struct
- **Cohesion**: each file covers one concern; split large files by feature, not
  by number suffix
- **Coupling**: minimize public interface per layer and per feature; prefer
  private helpers
- **Naming**: files use descriptive names, never numbered copies (`_1`, `_v2`)
- **Docs**: every new doc produces a `xxxx_tldr.md` (≤30 lines + diagram)

### Strictness Tiers (lint-tier axis)

Code-strictness is a `moderate | lib | reliable` tier, **orthogonal** to the
stdlib memory tiers (`nogc_sync_mut`, ...) — never conflate the two. `reliable`
is the strict-lint + (planned) primitive-use + proof-coverage ladder that
supersedes the rejected "High-robustness mode". Select via `simple.sdn [lints]
profile=`, `simple lint --profile=<tier>`, or a `@lint_profile(<tier>)` file
header (most-local-wins; distinct from the R9 `@profile(critical)` must-use
annotation). Unset = legacy defaults. Every lint code is configurable via
`[lints]` / `@allow`/`@warn`/`@deny`. Guide: `doc/07_guide/language/strictness_tiers.md`
(tldr alongside); plan: `doc/03_plan/compiler/reliable_mode/reliable_mode_plan.md`.

## Feature Module Packaging (`.sfm`)

When a feature ships a runnable module, package it as a **Simple Feature Module**
(`.sfm`): embed the compiled SMF as an opaque payload plus a feature manifest
(exposed front-end/back-end layers + `SfmSecurityLevel`; mark `Trusted` only when
privileged layers must be gated). Consume it via `std.sfm`: `sfm_load` parses the
container, `sfm_resolve` resolves a manifest layer (DI wires layers from the
manifest; an AOP authz aspect enforces the security level). See
[`doc/04_architecture/infra/sfm/simple_feature_module.md`](../../doc/04_architecture/infra/sfm/simple_feature_module.md)
and [`doc/05_design/infra/sfm/simple_feature_module.md`](../../doc/05_design/infra/sfm/simple_feature_module.md).

## Performance Checking & Cross-Language Comparison

To verify correctness across execution modes and benchmark against other languages:

- **Guide:** [`doc/07_guide/compiler/check_perf.md`](../../doc/07_guide/compiler/check_perf.md) — interpreter / SMF loader / native mode checks + cross-language perf matrix
- **Harness:** `sh scripts/check/check-cross-language-perf.shs` — measures size, cold startup, warm throughput (fib35), parallel spawn + binary sizes + peak RSS (baseline-subtracted per-worker delta) against bun, python, go, erlang, java, C. Use `RUN_TIMEOUT=<seconds>` for bounded smoke or slow-host runs; the harness removes failed Simple outputs so stale native/SMF artifacts are not measured.
- **GUI perf:** `sh scripts/check/check-gtk-gui-size-speed-baseline.shs` — frame time, binary size, cache hit rates, peak RSS (Simple vs GTK; GTK measured inside xvfb-run)
- **Startup audit:** `sh scripts/check/check-startup-size-performance-audit.shs` — cold startup, binary size, ELF sections, library deps, peak RSS
- **TL;DR:** [`doc/07_guide/compiler/check_perf_tldr.md`](../../doc/07_guide/compiler/check_perf_tldr.md)

Correctness quick-check across all modes:

```bash
for mode in interpreter smf native; do
    bin/simple test path/to/spec.spl --mode=$mode
done
```

For concurrency perf work, do not collapse the Simple APIs into one "thread"
bucket. `thread_spawn` is the OS-thread primitive,
`cooperative_green_spawn` / `cooperative_green_spawn_value` in
`std.concurrent.cooperative_green` are cooperative queue APIs on the current OS
thread, `multicore_green_spawn` is the Pure Simple bounded-worker facade that
must prove `used_runtime_pool()` for M:N claims, and `task_spawn` is the
lower-level task facade over `multicore_green_spawn`. Keep
`doc/07_guide/lib/misc/stdlib.md`, `doc/07_guide/compiler/check_perf.md`, and
`.codex/skills/coding/SKILL.md` updated when those surfaces change.

Concurrency API misuse is enforced by `simple check` as the E-PAR rule family
(E-PAR-001..005: facade/alias/surface/call-shape/rt_pool rules; E-PAR-006:
cooperative/multicore green closures are share-nothing — no module-level
mutable `var` reads, no captured `var` writes; `thread_spawn` exempt). Both
compilers implement the
rules: the Rust seed in `driver/src/cli/check.rs`, the pure-Simple lints in
`src/compiler/35.semantics/lint/concurrency_{api_misuse,share_nothing}.spl`
wired into `src/app/cli/check.spl`. The self-hosted E-PAR-006 lane is fully
active — the parser lambda-argument gap (backslash lambda + block-in-parens) was
fixed; see `doc/08_tracking/bug/selfhosted_parser_lambda_gap_2026-06-11.md` for
the full fix record (remaining: superlinear parse perf at ~150+ lines). Fixtures:
`test/fixtures/concurrency_api_misuse/` + system spec
`test/03_system/feature/usage/concurrency_api_misuse_spec.spl`.

Native-mode SPipe specs are not always a reliable oracle for runtime ABI work:
unresolved generated BDD calls (`rt_bdd_*` / `std.spec`) can no-op or segfault
before `it` bodies execute. For native runtime hooks, pair interpreter SPipe
coverage with a direct native entrypoint that uses hard `rt_exit` checks.

For Pure Simple SSH/HTTPS server lanes, keep protocol code in `.spl` and limit
runtime/SFFI to host access: TCP accept/read/write, time, entropy,
filesystem/cert/key access, and process execution. `release` mode is the
production Simple protocol path. `alpha` and `beta` may use native/SFFI protocol
wrappers only as explicit comparison paths. Do not let `rt_ssh_*` or
`rt_tls_server_*` silently replace Simple protocol behavior in release mode.
See `doc/07_guide/lib/networking/pure_simple_servers.md`.

Optimization must stay **pure Simple** (`.spl`) — do not modify Rust seed or C runtime.
Exception: safety-critical guards in process/signal paths (e.g. `pid <= 0` checks
before `kill()`/`waitpid()`) belong in the seed runtime too — a failed spawn's
`-1` reaching `kill(-1)` SIGTERMs every user process (tmux + all SSH sessions +
`systemd --user`). Such seed changes only take effect after a seed rebuild
through `scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy`.
Normal bootstrap reuses the Rust seed and never runs cargo. The wrapper's
`-c 'print(1+1)'` probe is only compiler sanity; the Stage 4 essential-tools
gate above must pass before claiming the pure-Simple toolchain is healthy (see
`.claude/rules/bootstrap.md`).
See `doc/07_guide/runtime/process_kill_safety.md`.

### Bootstrap gate uses the deployed `bin/release`, not the Rust seed

`bin/simple build bootstrap` Stage-1 worker is the **deployed self-hosted**
`bin/release/<triple>/simple` (it self-execs — `interpreter: bin/release/.../simple`),
NOT `target/release/simple` or `target/bootstrap/simple`. `SEED=`/`SIMPLE_SEED=`
redirect only the bootstrap *driver*, not the Stage-1 worker. Consequence: when a
new `rt_*` extern lands in `.spl` (e.g. `rt_lexer_source_set` in `lexer.spl`), the
worker's stale native-build extern allowlist rejects it (`unknown extern function:
rt_lexer_source_set`) even though both Rust seeds accept it — a **circular redeploy
wall**: `bin/release` can only be refreshed by a bootstrap that runs `bin/release`.
This is the known-hard whole-compiler redeploy (memory: "#99 whole-compiler
redeploy — do NOT race"). Unblock by refreshing
`bin/release/<triple>/simple` from a CURRENT compiler via the `cp` to `.new` + `mv`
pattern (direct `cp` hits "Text file busy" when in use), then re-run the gate. So a
central-compiler resolver change is only *verified* after this refresh — a
probe-green interpreter run is not the bootstrap gate.

### SimpleOS freestanding-.spl discipline (kernel-path specs/code)

Three proven traps when Simple code targets the freestanding kernel
(x86_64-unknown-none) — each cost a debugging arc; all documented in
`src/os/kernel/loader/fs_exec_resolve.spl`'s header:
1. Module-level array/`[text]` initializers DO NOT RUN (garbage + fault on
   `.len()`): use function-returning constants + lazy-init behind a bool
   (scalar module vars land in zeroed .bss, so `false` is reliable).
2. class construction + trait-object dynamic dispatch corrupts ring-0 boot:
   use direct externs or @cfg dispatch in kernel paths.
3. `char_at`/`starts_with` are unreliable on DYNAMICALLY built strings:
   use the raw `[u8]` accessor pattern (rt_string_to_byte_array +
   rt_bytes_u8_at).
Also: deep-call-stack spawn/exec calls overflow the kernel stack — call
spawn-like entries from shallow frames (sshd accept loop, not packet
handlers). Current host-OS state + lane map:
`doc/07_guide/os/simpleos_host_os_guide.md` and
`doc/03_plan/os/simpleos/host_os_completeness_plan.md`.

### SimpleOS board-proxy evidence: OVMF pflash, never `-kernel`

For SimpleOS "board-runnable" claims, QEMU `-kernel` runs are NOT board
evidence — they bypass real firmware (the design ban: "no QEMU-only
mechanism"). The board-proxy gate is **OVMF pflash + GRUB-EFI**
(`scripts/os/scp_retrieve_over_ssh_uefi.shs` is the reference: boots the
128 MB-base kernel `linker_128mb.ld`, SSH → in-guest clang compile → `getfile`
byte-exact object → exit 7). Layout invariant to respect in any OS spec that
links or mmaps user memory: the OVMF kernel `.bss` band is
`[0x08000000, ~0x16400000)`; ring-3 payloads link at `0x40000000`, mmap base
`0x50000000` (`sysroot.shs` / `syscall.spl`). Evidence bar for any board-proxy
PASS: a durable serial transcript with the full ladder — never a verbal claim
(the 2e "FULL COMPLETE" mislabel was caught exactly this way). Physical-board
phases: `doc/03_plan/os/simpleos/hw_qemu/clang_board_bringup_x86_64_uefi.md`.

For SimpleOS QEMU host-GPU external-host evidence, use the postponement and
resume contract in `doc/07_guide/platform/simpleos/qemu_system_tests.md` and
the authoritative TODO matrix in
`doc/03_plan/agent_tasks/simpleos_qemu_host_gpu_external_host_evidence.md`.
Reuse its existing TODO owners: postpone only prepared Windows DirectX, macOS
Metal, NVIDIA CUDA, and the non-current native-host portions of TODO 563, TODO
569, TODO 570, and TODO 566; keep their current Linux Vulkan portions and all
hardware-independent TODO 566 source/parser/self-test work active. NFR-006
requires one guest-observed interval from device initialization through every
rejected or timed-out backend attempt to selection or CPU fallback. Daemon
HELLO `elapsed_us` and TCG are correctness evidence only; they cannot close the
500 ms native row. Resume only
on the prepared native host with a
pure-Simple compiler accepted by `simple_binary_is_valid`. Source inspection,
emulation, screenshots, cached reports, synthetic handles, or CPU mirrors are
not native PASS evidence; require device-origin readback, stable identity,
exact CPU-oracle parity, correlated IDs, and final high-capability review.

For memory-perspective work (gc/nogc boundary, leak checks, alloc enforcement):
the gc-boundary lint (`gc_boundary_crossing`) resolves alias shims via
`GC_ALIAS_MANIFEST` — kept in sync in BOTH compilers
(`src/compiler/35.semantics/gc_boundary_check.spl` and Rust seed
`src/compiler_rust/compiler/src/lint/checker_resources.rs`); update both when a
new gc_*-backed shim is added. Tooling research + 3-tier on/off recommendation:
`doc/01_research/runtime/memory_tooling/`. Open findings:
`doc/08_tracking/bug/gc_nogc_memory_audit_findings_2026-06-11.md`.
Mode escalation: interpreter (dev) → SMF (staging) → native (production).

## Dependency hygiene during refactoring

When refactoring imports or adding new `use` statements, run:

```bash
bin/simple deps fast   <entry.spl>   # cycle check + closure size
bin/simple deps normal <entry.spl>   # exclusive vs shared cost per import
```

Gates before merging:
- No new cycles (`fast` CYCLES section must be empty or pre-existing only).
- Closure growth is justified (a large exclusive count for a single-symbol
  import is a smell — import the submodule directly instead).

Avoid hub imports (`export use x.*` re-export hubs) for single symbols: one
such import can drag in hundreds of files (see `deps_tool.md` case study).
This is the same rule that caused `app.io` hub to break `deep_report.spl` at
startup — the `deps normal` exclusive column is the detector.

## Lib tier rule (default = nogc_async_mut)

`src/lib/nogc_async_mut/` is the default stdlib tier: every stdlib feature
must be reachable there. New stdlib features land in `nogc_async_mut` first
(pure Simple); other tiers (`nogc_sync_mut`, `gc_async_mut`,
`nogc_async_mut_noalloc`) only hold deliberate optimized/specialized
variants. A feature that exists only in another tier is a gap — close it
with an `export use <tier>.<module>*` wrapper in `nogc_async_mut`
(wrapper first, native port second). `common/` stays tier-neutral pure
functions. See `doc/04_architecture/lib/runtime_family_tier_defaults.md`.

Export strictness (E0410): `pub val` alone exports nothing — add explicit
`export NAME` statements; shims need `export use X.*` (plain `use` re-exports
nothing); stale sibling `.smf` files shadow `.spl` edits. Full rules:
`doc/07_guide/language/module_system.md` (E0410 section).

References:
- Full guide: `doc/07_guide/compiler/deps_tool.md`
- Lazy parsing prior art: `doc/01_research/compiler/parser/lazy_parsing_prior_art.md`
- Tier defaults ADR: `doc/04_architecture/lib/runtime_family_tier_defaults.md`

## Network types & algorithms (fully-typed layer)

When a task touches networking, protocols, wire codecs, or crypto/compression
algorithms, follow the typed-layer map — do not invent a parallel type or
reimplement an existing algorithm:

- **General network custom types** → `src/lib/common/net/` (`byte_cursor`
  big-endian `ByteReader`/`ByteWriter`, `addr`, `oid`, `ber`, `net_time`,
  `routing`, `anti_replay`). A type used by ≥2 protocols is promoted here.
- **App protocols** → `src/lib/nogc_sync_mut/<proto>/` (+ `<proto>/secure.spl`
  for the X-over-TLS wrapper). **L3/L4** → `src/os/services/netstack/`.
- **Algorithms** (reuse, never reimplement) → `src/lib/common/{crypto,compress,
  hash,base64,base_encoding,huffman,rsa,signature,jwt,...}`; verify against
  RFC/NIST known-answer vectors (never self-comparison — see false-green guard).
- **Custom-typed algorithm layers** (additive, wrap the primitive cores — never
  rewrite them): `src/lib/common/search/` (types + exact/prefilter/inverted
  index + BM25/TF-IDF + IVF/kNN ANN + roaring, fixed-point not f64),
  `src/lib/common/crypto/typed/` (`Digest`/`MacTag`/`Nonce`/`AuthTag`/
  `Plaintext`/`Ciphertext`/`SecretKey`/`PublicKey`/`Signature`/`SharedSecret`
  on `ByteSpan`, constant-time `ct_eq`; hashes/aead/asym + alpha `seam`),
  `src/lib/common/compress/typed/` (`LzToken`/`SymbolFreqs`/`HuffTable` + lz4/
  deflate/zstd/lzma2). Shared byte foundation = `src/lib/common/bytes/`. These
  ride the **alpha dual-backend** fail-closed seam (`src/os/crypto/
  dual_backend.spl`, guide `doc/07_guide/os/crypto_dual_backend.md`).
- **Conventions:** integer `val` constant dispatch (not payload enums); wire
  codecs on `ByteReader`/`ByteWriter`; parse loops offset-based/inline (never a
  free fn taking a reader by value); cross-module array helpers must return.
- Full guides: [`doc/07_guide/lib/networking/typed_network_and_algorithms.md`](../../doc/07_guide/lib/networking/typed_network_and_algorithms.md)
  (tldr alongside) and, for the search/crypto/compress custom-typed layers,
  [`doc/07_guide/lib/algorithms/typed_alpha_algorithm_layers.md`](../../doc/07_guide/lib/algorithms/typed_alpha_algorithm_layers.md).
- **JIT tuple-return gotcha:** network externs that return a tuple (e.g.
  `rt_http_request → (status, body)`) read as garbage in default JIT on builds
  before commit `49ca9697987` — cranelift unboxed the bridged composite result.
  Run such specs on a build that includes the fix, and assert on **both** tuple
  fields (`.0` and `.1`), not just `.0` — a spec that only checks the status
  passed even while the body was corrupted. Same hazard for text-returning
  externs. Bug: `doc/08_tracking/bug/itf_minio_sigv4_not_runnable_interp_or_native_2026-06-16.md`.

## Run

```
bin/simple test path/to/my_spec.spl
```

## Var-resolution lanes (`variants/` overlay)

Use this section when a lane touches `variants/` (the resolver-only variant
overlay), `variants/__init__.spl`, resolver root ordering, variant profile
selection, default fallback, or DI module selection. Background:
`doc/03_plan/compiler/module_resolution/var_resolution_plan.md`.

Hard rules:

- **No new grammar.** `var` is the mutable-variable keyword; never make `var.*`
  or `variants.*` an importable namespace. Source imports stable module names;
  SDN config selects the active variant.
- **`variants/` is the on-disk root** (vocabulary stays `var:` / `--var` /
  `SIMPLE_VAR_*` / `E-VAR*`). Do not reuse `var/` — it is FHS runtime state.
- Parse `variants/__init__.spl` with the bootstrap-safe line reader
  (`var_parse_manifest`), not the full SDN parser (resolver precedes it).

Required SSpec coverage before PASS:

- selected variant root resolves before any default root; any selected root
  before any group/global default root; group `order` breaks selected-vs-selected
  ties deterministically;
- group `default`, global `variants/default`, and `src` fallback each covered;
- missing `default` fails when `default_required: error`; unknown group/value
  fails; direct `var.*`/`variants.*` import is rejected;
- DI service declarations keep stable `module:` paths and resolve through the
  active var profile (DI selects at build time, when the factory module loads);
- **resolver cache keys include the active var fingerprint** — assert the cache
  invalidates across `--var-profile` changes in BOTH the Rust seed and the
  self-hosted Simple resolver (the Simple cache key historically omitted even the
  SIMD tier — parity is part of acceptance).

Generated manuals must show the active `config/var.sdn`, the candidate root list,
the selected resolved path, and fallback evidence. A stale
`doc/07_guide/compiler/module_resolver.md` / `var_resolution.md` or generated
`doc/06_spec/...` manual is a verify failure, not release cleanup.

### Seam qualification bar (before migrating ANY subsystem into `variants/`)

A candidate seam may be migrated ONLY if it passes BOTH:

1. **Real existing variation** in the code today — two+ genuine implementations of
   one interface, or real branching behind one interface. Refactor OUT existing
   logic; never invent a backend just to fill a group (violates no-unused-code).
2. **Genuine build/deploy-target choice, not a runtime-host/per-call decision.**
   The overlay resolves at COMPILE time, so the chosen variant is baked into the
   binary. A runtime-host value (host OS, negotiated content-encoding) or a
   per-call argument baked at build time REGRESSES correctness.

Rejected examples (recorded in `doc/08_tracking/bug/var_overlay_*`):
`path_separator` (runtime host), `encode_<arch>` (compiler is multi-target at
runtime — one binary emits all arches), crypto `constant_time` (no real alt
backend without FFI), compress codec (runtime-parameterized: codec is a per-call
arg / `Accept-Encoding` negotiation). An honest "no qualifying seam — needs
precondition X" is the correct deliverable when none passes; never force a weak
or behavior-breaking variant.

### Safe migration pattern (proven: ui.renderer, os platform-ext)

- Keep the EXISTING import path as the stable name; mirror its exact segments
  (including any leading `std`/`lib`) under `variants/<group>/<value>/<segs>.spl`.
  Change ZERO importers; create only non-default variant dirs (NOT `.../default`)
  so the default profile provably falls through to the canonical `src` impl.
- Make the canonical (src) seam preserve today's behavior exactly: delegate one
  selection point (e.g. `renderer_priority_order()`, `target_lib_ext()`); keep all
  implementations compiled in and any runtime override intact.
- Keep the active profile inert by default — `auto`/`default` create no selected
  root (a literal selected value like `cpu` IS a live root: a `config/var.sdn`
  `dev` footgun).

### Tooling: `simple var`

`simple var {list,check,roots,resolve <module>}` (`src/app/var/main.spl`,
`--var-profile <name>` override) inspects the active overlay: groups/values,
manifest validation (excludes the `auto` sentinel), active candidate roots, and
the resolved candidate file for a stable import. Use it in verify evidence
instead of hand-tracing resolution.
