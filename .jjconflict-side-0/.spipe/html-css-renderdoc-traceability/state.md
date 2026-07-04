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
- AC-7: The top-level GUI/web/2D Vulkan RenderDoc runbook is macOS-only for now, records MoltenVK readiness separately from Chrome/Electron ANGLE Vulkan and RenderDoc readiness, and defers Windows/Linux capture gates until separate runbooks are added.

## Scope Exclusions
Do not detach or rebind host GPUs to `vfio-pci` without explicit privileged operator approval.

## Phase
dev-done

## Log
- dev: Created state file with 6 acceptance criteria (type: feature).
- dev: Added macOS/MoltenVK portability probe to the plan. macOS evidence can supplement the investigation, but only original RenderDoc+Chrome Vulkan `.rdc` evidence closes the remaining Linux gate.
- impl: Added `scripts/check/check-gui-renderdoc-feature-coverage-status.shs` as a non-launching restart audit for HTML/CSS traceability, WidgetKind HTML renderer dispatch, Electron layout manifest scope, production GUI/web parity evidence, and the active RenderDoc gates.
- verify: 2026-06-19 `sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs` reports all 43 `WidgetKind` HTML dispatches covered and the 18-case Electron Simple Web layout manifest recorded. The gate remains incomplete because local Simple RenderDoc evidence is missing (`simple_renderdoc_reason=missing-simple-rdoc`) and original Chrome/Vulkan external RenderDoc capture is unavailable without a host-side `.rdc`.
- docs: 2026-06-21 updated the GUI/web/2D Vulkan RenderDoc guide and UI GUI feature skill to make the top-level workflow macOS-only. Windows and Linux are explicitly deferred and must reuse the same evidence keys when their platform capture gates are added later.
- docs: 2026-06-25 Linux Vulkan-backed browser lane is now provisioned and verified on an Ubuntu 24.04.3 / Intel RPL-P host (Mesa ANV, Vulkan 1.4.318). Electron `v42.5.0` (`~/electron-vulkan`, `vulkan: enabled_on`) and Chrome `139.0.7258.138` both confirmed rendering through ANGLE→Vulkan; RenderDoc `v1.44` CLI installed (`/opt/renderdoc`, Vulkan-capable). Recorded the full Linux Status/Install/Readiness section in `doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md` and a Linux-availability note in `.claude/skills/lib/spipe_ui.md`. **Mandatory Wayland gotcha:** Chromium Vulkan requires `--ozone-platform=x11` (else software fallback). **Open Linux gates (partial AC-5/AC-6):** RenderDoc is installed but no `.rdc` capture produced yet; Chrome GPU-process hooking is blocked by `renderdoc-chrome-gpu-sandbox-localtime64_r` (the `--disable-gpu-sandbox` GPU process crashes with `undefined symbol: localtime64_r`). Electron capture path (`capture-renderdoc.sh`, `--in-process-gpu --no-sandbox`) is wired but `.rdc` evidence still pending.
