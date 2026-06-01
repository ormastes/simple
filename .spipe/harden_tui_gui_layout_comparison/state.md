# Feature: harden-tui-gui-layout-comparison

## Raw Request
$sp_dev harden tui and gui layout comparison and fix. and optimize size and perf with (metal, vulkan, cuda, simd cpu) also. research web and local and plan and design deeply.

## Task Type
feature

## Refined Goal
Create a verified plan and implementation path that hardens TUI/GUI layout comparison, fixes discovered comparison defects, and designs measurable size/performance optimization paths for Metal, Vulkan, CUDA, and SIMD CPU backends.

## Acceptance Criteria
- AC-1: Local research identifies the current TUI, GUI, layout, renderer, capture, and comparison code paths, existing tests, known bugs, and size/performance constraints.
- AC-2: Domain research records current external practices for visual/layout regression testing, UI diff tolerances, GPU backend performance, binary size control, and CPU SIMD optimization, with sources.
- AC-3: Requirement options and NFR options are written with pros, cons, and effort estimates, and final requirements are created only after user selection.
- AC-4: Architecture and detail design define a TUI/GUI layout comparison contract, failure triage model, fixture/capture strategy, tolerance rules, and cross-backend optimization plan for Metal, Vulkan, CUDA, and SIMD CPU.
- AC-5: SPipe system specs cover matching layouts, intentional mismatch reporting, capture reproducibility, and backend/performance evidence gates without placeholder assertions.
- AC-6: Implementation fixes discovered TUI/GUI layout comparison defects and preserves existing GUI/TUI behavior.
- AC-7: Verification includes relevant Simple checks/tests, generated scenario manuals, no executable specs under doc/06_spec, and evidence for size/performance targets or explicitly tracked follow-up bugs where hardware/runtime coverage is unavailable.

## Scope Exclusions
Shipping production GPU compute kernels for every backend is excluded unless selected requirements explicitly require it; the minimum scope is a designed and testable backend strategy with evidence gates and implemented fixes for currently reachable comparison defects.

## Phase
dev-done

## Log
- dev: Created state file with 7 acceptance criteria (type: feature).
