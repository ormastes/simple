# browser (Simple Browser) Feature Expert

## Role

Own feature-specific process knowledge for **Simple Browser** — the
`app.ui.render`-contract browser app (`src/app/browser/`). Use this skill
when work touches `src/app/browser/`, its wiring into
`src/app/wm_showcase/`, or its specs.

## Pipeline Links

Invoke as slash-commands (`/research`, `/design`, …); sources live in `.claude/skills/`:
[research](../../../../.claude/skills/research.md) ·
[design](../../../../.claude/skills/design.md) ·
[impl](../../../../.claude/skills/impl.md) ·
[verify](../../../../.claude/skills/verify.md) ·
[release](../../../../.claude/skills/release.md) ·
[spipe](../../../../.claude/skills/spipe.md) (spec-writing landmines)

## Feature Links

- [Source](../../../../src/app/browser/) — `main.spl` (CLI entrypoint,
  mirrors `src/app/terminal/main.spl`'s shape), `render_adapter.spl`
  (`render_browser`/`render_browser_html`/`render_browser_text`, the
  `app.ui.render.types.RenderConfig`/`RenderResult` contract ~20 sibling
  apps already use — terminal, ide tools, dashboard, office, ...)
- Consumer: [`src/app/wm_showcase/session.spl`](../../../../src/app/wm_showcase/session.spl)
  — the "Simple Browser" showcase window feeds `render_browser_html(...)
  .html_output` through the same
  `simple_web_render_html_to_readback_result_with_engine2d_backend` cascade
  + layout + paint path every other HTML-backed showcase window uses; the
  window opens `simple://home`, the real Hello World page
  (`browser_page_body_html`), not a placeholder/pixel shortcut.
- Glossary: [Simple Browser](../../../glossary.md#simple-browser)
- Sibling apps this mirrors: [terminal feature expert](../../feature_expert/)
  (if/when one exists) — see `src/app/terminal/render_adapter.spl` for the
  identical contract shape.

## Relationship to other "browser" things in this repo (do not confuse)

Three unrelated modules share the word "browser" — know which is which
before touching any of them:

1. **`src/app/browser/`** (this feature) — hosted, `app.ui.render`-contract
   app. Runs in-process, pure function in → HTML/text out. No event loop of
   its own.
2. **`src/os/apps/simple_browser/`** — baremetal/freestanding-only.
   `spl_start()` entry, VFS externs, boots as a QEMU kernel directly via
   `native-build --entry-closure --target x86_64-unknown-none`. Cannot run
   in a hosted session; do not try to reuse it for hosted work.
3. **`src/app/ui.browser/`** — a standalone winit-windowed GUI-widget-tree
   app with its own event loop and host window (`app.spl`/`main.spl`), not
   an `app.ui.render`-contract app. Predates this feature; not touched by it.

## Update Rule

When the project process creates or changes research, requirements,
architecture, design, tests, implementation, verification, or release
artifacts for this feature, update this skill with the new links and the
current handoff notes.

## Handoff Notes (2026-08-06)

- **Created this session**: `src/app/browser/render_adapter.spl` (new),
  `src/app/browser/main.spl` (new), wired into
  `src/app/wm_showcase/session.spl` (new `WmShowcaseWindowSpec` entries for
  `kind: "browser"` and `kind: "terminal"`; desktop height grown 360→430 to
  fit a second HTML-window row without overlap).
- **Recovered once already**: the first landing of these files was silently
  reverted by a shared-working-copy race (a known hazard class in this repo
  — see `[[reference-shared-wc-environment-traps-2026-07-30]]` in memory)
  before it could be committed. Recreated verbatim from the original
  authoring context; land promptly via plumbing CAS next time rather than
  leaving new files uncommitted in the shared tree for long.
- **Spec-tested since 2026-08-06** (supersedes the earlier "not yet
  spec-tested" note): `test/01_unit/app/browser/browser_render_adapter_spec.spl`
  (9 examples, pure dispatch/content logic — engine calls deliberately
  excluded, one alone blows the spec runner's 10M-op budget) and
  `test/02_integration/app/browser_cli_log_modes_spec.spl` (4 examples,
  process-spawns the real CLI). The wm_showcase pixel-parity gate remains
  separately tracked in
  `doc/08_tracking/bug/wm_showcase_session_capture_spec_no_examples_executed_2026-08-06.md`.
- Full HTML-window renders in this environment cost 30-50 CPU-minutes each
  (interpreted cascade+layout+paint) — the wm_showcase suite now has 4
  HTML-backed windows (gui, web, browser, terminal) instead of 2, so a full
  `wm_showcase` spec run costs roughly double what it did before this
  change. Budget accordingly; do not run it synchronously inline.
- **`--open` real-GUI window landed 2026-08-06** (`115e1b522b6` +
  `88df83a75e5` idle-poll fix + `bb106fcc335` fallback fix):
  `main.spl --open` opens a real winit window via `GuiRenderer`, presents
  one engine frame, blocks until close. End-to-end verified under
  Docker+Xvfb (window on screen with real glyph pixels in 59s); usage guide:
  `doc/07_guide/app/browser.md`.
- **Load-bearing structure — do not "clean up"**: `main.spl` renders the
  pixels and passes them into `run_browser_window_gui(url, w, h, pixels)`.
  Moving the render into `gui_window.spl` looks tidier but silently drops
  the entire engine into the tree-walk interpreter (~10-50x, no diagnostic;
  four 1800s-budget runs never finished before the hoist). Compiler defect:
  `doc/08_tracking/bug/gui_window_caller_frame_silent_interp_fallback_2026-08-06.md`.
- **2026-08-15 session lanes** (specs under `test/01_unit/browser_engine/`):
  - **Vulkan render lane**: `render_lane.spl` gained a `vulkan` lane
    (CPU paint → engine2d `VulkanBackend` present → `device_readback`,
    fail-closed provenance — never labels software pixels "vulkan");
    `browser_renderer.spl create_with_backend` routes `vulkan`/`webgpu`
    through `Engine2D.create_requested_backend` instead of silently
    degrading. Gate: `browser_vulkan_lane_spec.spl`. Docker lavapipe
    end-to-end: `scripts/check/check-simple-web-browser-docker-vulkan.shs`
    (needs a `simple-runtime/vulkan`-featured build at
    `build/browser-vulkan/simple`; `simple-compiler/vulkan` still blocked on
    an incompletely vendored rspirv — see
    `doc/08_tracking/bug/browser_has_no_vulkan_render_lane_2026-08-15.md`).
  - **Script execution + animation clock**: page `<script>` (JS and
    `text/simple`) executes pre-paint; `browser_engine_animated_frames`
    (render_adapter) drives rAF/CSS clocks per frame. The nogc JS subset
    parser now supports `function name() {}` DECLARATIONS (it previously
    dropped them AND the statement after the closing brace). Gates:
    `browser_script_execution_spec.spl`, `browser_animation_clock_spec.spl`.
  - **Sandbox**: research + gap list in
    `doc/01_research/app/browser/browser_sandbox_model_research_2026-08-15.md`;
    page-script node natives (`require("process")`/`os`, `process.exit/cwd`)
    are now capability-gated (default DENY in `JsRuntime.new_browser`).

## Handoff Notes (2026-08-15, renderer hardening session)

All lanes below verified green this session. Run pattern for specs:
`SIMPLE_TIMEOUT_SECONDS=600 bin/simple test --no-session-daemon <spec>`; add
`SIMPLE_COVERAGE=1` for recordable-coverage runs (quirk: coverage is only
recorded on that flag, and the collector has known decision-skips — see bug
records `coverage_collector_skips_pub_val_and_match_heads_2026-08-15.md` and
`coverage_probe_plan_skips_struct_method_decisions_2026-08-15.md`).

- **Chrome counterpart provider**: `src/lib/nogc_sync_mut/spec/evidence/counterpart/chrome_dom_snapshot_provider.spl`
  — real Chrome over pure-Simple CDP at boundary `chrome.dom_snapshot@1`.
  Spec: `test/01_unit/infra/counterpart/chrome_counterpart_compare_spec.spl`.
  Details in the [counterpart_conformance expert](../counterpart_conformance/skill.md).
- **Coverage closure**: ~40 `*_coverage_closure_spec.spl` files under
  `test/01_unit/browser_engine/` drive renderer modules (layout, style,
  paint, dom color, file renderers) to 100% recordable branch coverage.
  Counterpart-side closure record (link, don't duplicate):
  `doc/08_tracking/test/counterpart_branch_coverage_closure_2026-08-15.md`.
- **Vector-font differential lane**: `tools/vector_font_diff/`
  (`run_vector_font_diff.shs`, `chrome_vector_font_dump.js`,
  `simple_vector_font_dump.spl`, outputs in `out/`) + system spec
  `test/03_system/browser_engine/chrome_vector_font_differential_spec.spl`.
  See also [vector_fonts expert](../vector_fonts/skill.md).
- **Docker+Vulkan system lane**: `scripts/check/check-simple-web-browser-docker-vulkan.shs`
  (lavapipe in Docker) now gated by
  `test/03_system/browser_engine/docker_vulkan_browser_spec.spl`.
- **Interpreter fixes landed**: ClassInstance `simple` handling and nested
  field-index assignment — unblocked several of the coverage specs above
  (related record: `engine2d_landing_blocked_on_classinstance_seed_infra_2026-08-15.md`).

## Handoff Notes (2026-08-16, sandbox gate wiring)

- **The seccomp allow-list self-check was orphaned.**
  `src/runtime/test/rt_browser_renderer_seccomp_allowlist_selfcheck.c` landed
  2026-08-15 with the deny-list→allow-list fix and was invoked by **nothing** —
  no runner, no spec, no wrapper. The jail's strongest evidence was unreachable
  from any gate. Now wired by
  `scripts/check/check-browser-renderer-sandbox-seccomp.shs` (fail-closed:
  no-seccomp kernel and no-C-compiler host both give `ERROR — nothing was
  checked`, exit 2), gated by
  `test/03_system/browser_engine/browser_renderer_sandbox_spec.spl`
  (REQ-WEB-BROWSER-014, SANDBOX-N/E/D). Gate ran here: `PASS — 3 check(s)
  verified`, real `SIGSYS` kill on `socket()`.
- **Build trap**: the self-check needs
  `-ffunction-sections -fdata-sections -Wl,--gc-sections`. `runtime_process.c`
  drags in spawn/fork paths referencing `rt_array_len`/`rt_string_data`/`rt_fork_*`
  that a single-TU build cannot link; they must be dead-stripped. Cost one fix
  cycle — the sibling `run_process_piped_write_test.shs` already did this and is
  the pattern to copy.
- **Evidence split is deliberate.** The gate is native C-runtime evidence and it
  passed. The SSpec scenario is **unexecuted** — no admitted pure-Simple runtime
  on this host, and Rust-seed output is not evidence for this lane. So
  REQ-WEB-BROWSER-014 is **not promoted**. Do not read the green gate as a
  promoted production row.
- **Still open, do not claim covered**: problems 2 and 3 of
  `browser_seccomp_denylist_and_inprocess_unjailed_2026-08-15.md` — no
  namespace/privilege drop, and in-process browsers under `src/app/browser/**`
  still evaluate page script unjailed. The gate proves the jail's syscall
  contract, not that every browser surface enters it.

## Handoff Notes (2026-08-16, second pass — namespaces)

- **Problem 2 of the seccomp bug is now fixed** (user/net/IPC namespaces +
  uid/gid drop). The one thing to know before touching it: the order
  `namespaces -> landlock -> seccomp` is NOT rearrangeable. Landlock's ruleset
  has no allow rules, so it kills every write including `/proc/self/uid_map`;
  the seccomp allow-list has neither `unshare` nor `openat`. Move the namespace
  step after either one and the uid drop becomes impossible.
- **Do not make namespace failure fatal.** Ubuntu 24.04's
  `kernel.apparmor_restrict_unprivileged_userns=1` allows `CLONE_NEWUSER` but
  strips capabilities so `CLONE_NEWNET` gets EPERM. Hard-failing leaves NO jail
  on default Ubuntu — worse than seccomp+landlock. Posture is published via
  `rt_browser_renderer_namespaces_active()` instead.
- **To actually exercise the active path**: `docker run --privileged`. Default
  Docker and `--security-opt apparmor=unconfined` both still report
  `unavailable`, so they cannot prove the code works — only `--privileged` did
  (netns `net:[4026533421] -> net:[4026533540]`).
- **PID namespace is intentionally absent.** Don't "fix" it: `CLONE_NEWPID`
  only affects post-unshare children and `RLIMIT_NPROC=0` blocks forking.
## Handoff Notes (2026-08-16, layout box contract system coverage)

- **New system lane**:
  `test/03_system/browser_engine/layout_box_content_contract_spec.spl` states
  the `BeLayoutBox` contract that the `81684d8af46` layout/paint recovery
  settled — content rectangle derived per call from padding/border, element
  named by integer `node_id` and never by an embedded node object. Plan:
  `doc/03_plan/sys_test/browser_engine_layout_box_content_contract.md`; mirror:
  `doc/06_spec/03_system/browser_engine/layout_box_content_contract_spec.md`.
  Layer detail lives in
  [browser_engine layer expert](../../layer_expert/browser_engine/skill.md).
- **Why it exists**: the recovery deleted `_paint_box` (written against a
  nonexistent box shape) but left that shape with no system-tier statement, so
  the defect shape was unguarded. Scenario 3 mutates padding after construction
  — the only assertion that tells a derived content rectangle from a stored one.
- **Coverage boundary, recorded rather than padded**: `_apply_opacity` is
  excluded. Unit tier already closes all four branches, `StyleProps` has no
  `opacity` property, and it has zero product callers — there is no
  CSS-to-paint producer to integrate against.
- **TEST_BLOCKED**: never executed; no admitted pure-Simple CLI in this tree
  (`deployed_selfhost_test_subcommand_segv_blocks_bootstrap_2026-08-16.md`).
  Fail-closed by construction, so it verifies automatically once one exists.
  Do not report it as passing until it has run.

## Handoff Notes (2026-08-16, problem 3 groundwork)

- **The flip-line is now two predicates, deliberately.** `browser_sandbox_worker_routing_available()`
  = `browser_sandbox_routing_probe()` AND `browser_sandbox_render_route_wired()`.
  The probe is operator config (`SIMPLE_BROWSER_RENDERER_WORKER`); the second is
  code capability. Do NOT collapse them — setting an env var must never make the
  browser claim `jailed`.
- **What actually blocks the render route** (verified, not guessed): the broker's
  `render(kind, payload, timeout_ms)` returns `HostedBrowserRendererResult` whose
  payload is a `DrawIrComposition`, NOT `[u32]`; and no render call takes
  width/height (viewport is fixed at `create(generation, width, height)`, changed
  via `begin_resize`). So the app needs a rasterization step it lacks.
- **Do not add the worker arg to the CLI entry casually.** It is dispatched only
  at `src/os/hosted/hosted_entry.spl:285`; importing that into the CLI pulls
  `os.hosted.*` into every `simple` invocation's closure. That is a startup-cost
  design decision, which is why the executable is operator-supplied instead.
- **Layering is NOT the blocker.** 47 files under `src/app/` already `use os.*`.
- **Only the session paths run page script**: `browser_session_pixels_at_time`
  and `browser_engine_animated_frames`. `browser_render_html_to_pixel_array` is
  pure parse/layout/paint. Jail those two, not everything.
- **`to_not_contain` does not exist** despite ~10 specs under `test/03_system/`
  calling it. Use `expect(x.contains("...")).to_equal(false)`.
