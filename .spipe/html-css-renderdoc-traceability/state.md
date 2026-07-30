# Feature: html-css-renderdoc-traceability

## Raw Request
$sp_dev 1. find all html tags in most recent html spec. check all of them are assigned to sspec test if not add tests. 2. find all css tags in most recent css spec. check all is matched in sspec tests if not add tests. (make tag and tracability to one or more tests) 3. possible common combinations of html css combinations in sspec tests. especially, gui generated html/css combinations must checked. debug with simple 2d backed vulkan, and chrome on vulkan enalbed. use renderdoc(renderdoc cli) install it if not installed. check them in vulkan io level in renderdoc cli

## Task Type
feature

## Refined Goal
Provide executable SSpec traceability for current HTML elements, CSS properties, generated GUI HTML/CSS combinations, and Vulkan-backed browser rendering evidence through RenderDoc where the host environment permits it.

## Acceptance Criteria
- AC-1: The current WHATWG HTML element inventory is traced to one or more executable SSpec tests, with missing element coverage added.
- AC-2: The current W3C CSS property inventory is traced to SSpec coverage, with implemented properties covered by functional specs and unsupported properties explicitly inventoried.
- AC-3: Common generated-GUI HTML/CSS combinations are covered by executable SSpec tests.
- AC-4: Simple2D-backed Vulkan readback evidence passes on the local host.
- AC-5: RenderDoc CLI is installed and registered for Vulkan capture.
- AC-6: Chrome-on-Vulkan RenderDoc capture either produces Vulkan IO-level evidence or records a concrete host/environment blocker with non-repeated attempts and next required external action.
- AC-7: Platform runbooks keep macOS/MoltenVK evidence separate from
  Chrome/Electron ANGLE Vulkan/RenderDoc evidence. The provisioned Linux lane
  remains active with its concrete capture blocker; Windows remains deferred
  until a separate runbook is added.

## Scope Exclusions
Do not detach or rebind host GPUs to `vfio-pci` without explicit privileged operator approval.

## Phase
implementation-in-progress

## Log
- dev: Created state file with 7 acceptance criteria (type: feature).
- audit: 2026-07-29 independent behavioral review invalidated the inventory-only
  HTML/CSS PASS. HTML is currently 12 Full, 80 Partial, 11 unsupported,
  2 inventory-only, with 8 standard elements omitted by the checker inventory.
  The CSS 284 count is self-satisfying text inventory, at least 38 claimed
  properties are absent from canonical declaration owners, and retained
  generated-combination evidence is 13 pass / 25 fail. Created the missing
  behavior-first system-test and agent plans. AC-1, AC-2, AC-3, and AC-6 remain
  open; no qualified target-runtime PASS is claimed.
- dev: Added macOS/MoltenVK portability probe to the plan. macOS evidence can supplement the investigation, but only original RenderDoc+Chrome Vulkan `.rdc` evidence closes the remaining Linux gate.
- impl: Added `scripts/check/check-gui-renderdoc-feature-coverage-status.shs` as a non-launching restart audit for HTML/CSS traceability, WidgetKind HTML renderer dispatch, Electron layout manifest scope, production GUI/web parity evidence, and the active RenderDoc gates.
- verify: 2026-06-19 `sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs` reports all 43 `WidgetKind` HTML dispatches covered and the 18-case Electron Simple Web layout manifest recorded. The gate remains incomplete because local Simple RenderDoc evidence is missing (`simple_renderdoc_reason=missing-simple-rdoc`) and original Chrome/Vulkan external RenderDoc capture is unavailable without a host-side `.rdc`.
- docs: 2026-06-21 updated the GUI/web/2D Vulkan RenderDoc guide and UI GUI feature skill to make the top-level workflow macOS-only. Windows and Linux are explicitly deferred and must reuse the same evidence keys when their platform capture gates are added later.
- docs: 2026-06-25 Linux Vulkan-backed browser lane is now provisioned and verified on an Ubuntu 24.04.3 / Intel RPL-P host (Mesa ANV, Vulkan 1.4.318). Electron `v42.5.0` (`~/electron-vulkan`, `vulkan: enabled_on`) and Chrome `139.0.7258.138` both confirmed rendering through ANGLE→Vulkan; RenderDoc `v1.44` CLI installed (`/opt/renderdoc`, Vulkan-capable). Recorded the full Linux Status/Install/Readiness section in `doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md` and a Linux-availability note in `.claude/skills/lib/spipe_ui.md`. **Mandatory Wayland gotcha:** Chromium Vulkan requires `--ozone-platform=x11` (else software fallback). **Open Linux gates (partial AC-5/AC-6):** RenderDoc is installed but no `.rdc` capture produced yet; Chrome GPU-process hooking is blocked by `renderdoc-chrome-gpu-sandbox-localtime64_r` (the `--disable-gpu-sandbox` GPU process crashes with `undefined symbol: localtime64_r`). Electron capture path (`capture-renderdoc.sh`, `--in-process-gpu --no-sandbox`) is wired but `.rdc` evidence still pending.
- impl: 2026-07-29 commit `28f0e779b0d2` landed the bounded HTML-default
  tranche for `h1`–`h6`, `sub`, `sup`, valid-context fail-closed
  `selectedcontent`, and visible inline `slot` fallback. Canonical owners,
  behavior-first SSpec, and generated manual are present. Independent static
  review returned PASS and docgen evidence is complete with zero stubs. This
  is source/spec/manual evidence only; AC-1 and full HTML coverage remain open
  pending the remaining matrix and qualified execution.
- impl: 2026-07-29 commit `b17e868199af` landed the bounded CSS Grid foundation
  for explicit pixel tracks, gaps, placement/span, an implicit row, block
  control, and over-quota fail-closed behavior. The retained fixture,
  conformance checker, and pinned manifest truthfully remain `red-not-run`.
  Independent static review returned PASS and the generated Grid plus refreshed
  validator manuals are complete with zero stubs. AC-2 remains open: this is
  not complete Grid or full CSS coverage.
- verify: 2026-07-29 qualified SSpec execution remains blocked because the
  deployed pure-Simple wrapper fails its bounded test-ABI admission probe. The
  one direct artifact attempt segfaulted and was rejected; no Rust-seed or full
  bootstrap fallback was used. No executable PASS is claimed for either landed
  tranche. Overall phase remains implementation-in-progress/RED; AC-1, AC-2,
  AC-3, and AC-6 remain open.
- reconcile: 2026-07-30 exact repository HEAD
  `9653a09fdea118b5d502fa06989d83e12cd4fe19` contains the bounded `<small>`
  UA lane (`b9e1a0e6707`), script MIME boundary (`2211d8ae1b5`), HSTS history
  traversal (`416ccc6efb8`), input-button keyboard activation (`e9b50343645`),
  DrawIR text-transform repair (`e7af94e921c`), and shape-key StringBuilder
  optimization (`9653a09fdea`). These are static/evidence-held; the shape-key
  performance spec is unmeasured. JS `store_kind` remains RED design only at
  `f8b926e0dd5`. Stage-4 admission remains NONE: the active `4cdd` build is
  dirty/stale and has no receipt. D1 `1728` is held locally and MUST NOT MERGE;
  D2 stopped without a commit and remains pending review/unmerged. No runtime,
  full-browser, RenderDoc, performance, or goal PASS is claimed.
- reconcile: 2026-07-30 Batch 19 exact repository HEAD
  `165d7b3a8c799163e99321c56d0b4310c3b79fb4` contains bounded `<abbr>`
  inline-flow behavior (`8beb64585b2`), duplicate-offset keyframe source-order
  cascading (`2078c3dfab4`), and the hosted attachment-navigation activation
  boundary (`165d7b3a8c7`). All three are STATIC/EVIDENCE-HELD; animation
  runtime remains unavailable. Stage-4 admission is NONE: the `807182` build
  is dirty, divergent, and has no receipt. D1 and D2 remain held on lineage
  through `06dc5620781` and MUST NOT MERGE. D3 is STOPPED/UNCOMMITTED:
  `browser_session_runtime` retains two `SimpleScriptExecutor.reset` and three
  `BrowserRuntimeState.bind_dom` call sites. `browser_session_loading` retains
  two `SimpleScriptExecutor.bind_dom(current_dom)` and two
  `state.bind_dom`/`BrowserRuntimeState.bind_dom` call sites. SSpec, manual,
  and final review are incomplete; Lane 4 is untouched. Existing inventory
  and scenario counts remain governed by the canonical plans. No runtime,
  docgen, RenderDoc, performance, full-browser, goal, or aggregate HTML/CSS
  PASS is claimed.
