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
- AC-7: macOS/MoltenVK is tracked as a separate portability probe that can produce supplemental evidence or a concrete blocker, without replacing the original Chrome-on-Linux-Vulkan RenderDoc gate.

## Scope Exclusions
Do not detach or rebind host GPUs to `vfio-pci` without explicit privileged operator approval.

## Phase
dev-done

## Log
- dev: Created state file with 6 acceptance criteria (type: feature).
- dev: Added macOS/MoltenVK portability probe to the plan. macOS evidence can supplement the investigation, but only original RenderDoc+Chrome Vulkan `.rdc` evidence closes the remaining Linux gate.
- impl: Added `scripts/check/check-gui-renderdoc-feature-coverage-status.shs` as a non-launching restart audit for HTML/CSS traceability, WidgetKind HTML renderer dispatch, Electron layout manifest scope, production GUI/web parity evidence, and the active RenderDoc gates.
