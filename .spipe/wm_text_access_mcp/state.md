# Feature: wm_text_access_mcp

## Raw Request
research first, gui wm access through text access cli/service/mcp. check trace32 mcp. it access mdi windows on through text and manipulate. let same logic use wm access windows and other items in text. research it.

Continuation: $sp_dev make plan base researcha and impl

## Task Type
feature

## Refined Goal
Build a shared WM text-access layer that lets CLI, service, and MCP clients inspect and manipulate TRACE32 text/MDI windows, Simple UI surfaces, and host WM windows through one canonical snapshot/query/action model.

## Acceptance Criteria
- AC-1: Local and domain research artifacts exist for `wm_text_access_mcp` and identify TRACE32, Simple UI, host WM, and OS accessibility adapter constraints.
- AC-2: Selected feature and NFR requirements exist for `wm_text_access_mcp` before implementation begins.
- AC-3: Architecture and detail design documents define a shared adapter boundary, snapshot model, query/find behavior, action routing, capability metadata, staleness handling, and CLI/service/MCP surfaces.
- AC-4: System test plan and executable SPipe specs cover TRACE32-style text windows, Simple UI canonical access, WM top-level windows, unsupported operations, and hot-path behavior.
- AC-5: Implementation exposes a shared access core and at least first-step adapters for TRACE32 catalog/capture semantics, Simple UI access snapshots, and basic host WM top-level window access.
- AC-6: MCP/CLI/service entrypoints use the shared access core rather than duplicating backend-specific query/action logic.
- AC-7: Verification evidence proves selected requirements, NFRs, and system specs pass without placeholder assertions or doc/spec layout violations.

## Scope Exclusions
- Full UIA, AX, and AT-SPI platform adapters are excluded unless explicitly selected as the implementation option.
- Screenshot/OCR-only manipulation of arbitrary controls is excluded from the first implementation unless explicitly selected.

## Phase
dev-done

## Log
- dev: Created state file with 7 acceptance criteria (type: feature)
- plan: Added research-based agent task plan and system test plan.
- design: Added draft architecture and detail design based on recommended Feature Option B and NFR Option 2.
- gate: Implementation remains gated on explicit final requirement selection.
- requirements: User selected common window-to-text module extending TRACE32, Simple UI, and WM with NFR Option 2.
- impl: Added `src/lib/common/ui/win_text_access.spl` and re-exported it from `common.ui.access`.
- mcp: Added read-only `play_wm_text_status` status hook in the MCP play tool table and dispatch path.
- test: Added source-contract SPipe spec and mirrored manual for the first shared module/MCP contract.
- verify: `SIMPLE_LIB=src bin/release/simple test test/system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.spl --mode=interpreter --fail-fast` passed 10 examples; lints for touched implementation/spec paths passed; `sh scripts/check-mcp-native-smoke.shs` passed JSON/schema checks; `doc/06_spec` executable spec count is 0.
- verify-note: `SIMPLE_LIB=src bin/release/simple test test/integration/app/mcp_stdio_integration_spec.spl --mode=interpreter --fail-fast` did not pass because the current runner cannot parse unrelated modules such as `src/compiler/tools/lint/main_part3.spl`, `src/app/io/cli_compile_part1.spl`, and `src/std/common/spec/scenario_helpers.spl`; failures were outside the new WM text-access files.
