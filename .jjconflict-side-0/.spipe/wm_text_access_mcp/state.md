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
- verify: `SIMPLE_LIB=src bin/release/simple test test/03_system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.spl --mode=interpreter --fail-fast` passed 10 examples; lints for touched implementation/spec paths passed; `sh scripts/check/check-mcp-native-smoke.shs` passed JSON/schema checks; `doc/06_spec` executable spec count is 0.
- verify-note: `SIMPLE_LIB=src bin/release/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter --fail-fast` did not pass because the current runner cannot parse unrelated modules such as `src/compiler/tools/lint/main_part3.spl`, `src/app/io/cli_compile_part1.spl`, and `src/std/common/spec/scenario_helpers.spl`; failures were outside the new WM text-access files.
- blocker-fix: Normalized parser-sensitive multiline expressions/imports in MCP support paths, fixed process governor imports/state for interpreter execution, restored `bin/simple_mcp_server` delegation, and added a narrow safe-editor wrapper path for the stdio spec.
- verify: MCP stdio integration now passes 5/5 examples; WM text-access source-contract spec still passes 10/10; touched-path lint exits 0; `find doc/06_spec -name '*_spec.spl' | wc -l` prints 0; `sh scripts/check/check-mcp-native-smoke.shs` passes JSON/schema checks.
- impl: Made the window-to-text core public/importable, added a host-WM primitive-field snapshot helper for CLI/service/MCP callers, fixed parser-sensitive shared UI query serialization, and made the process shell result path public for MCP stdio tests.
- test: Upgraded the WM text-access SPipe spec from source-contract-only to 15 examples, including behavioral TRACE32, Simple UI, host WM, merged-query, supported-action, and unsupported-operation assertions.
- verify: `SIMPLE_LIB=src bin/release/simple test test/03_system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.spl --mode=interpreter --fail-fast` passes 15/15; MCP stdio integration passes 5/5; `bin/release/simple check src/compiler`, `src/lib`, `src/app/mcp`, and `src/app/simple_lsp_mcp` all report no errors; `sh scripts/check/check-mcp-native-smoke.shs` passes; `doc/06_spec` executable spec count remains 0.
- audit: Rechecked the current request against existing artifacts. Research,
  requirements, architecture, detail design, system plan, agent plan, SPipe
  spec, mirrored manual, implementation, MCP status hook, UI access guide, and
  `simple-ui` skill are present for `wm_text_access_mcp`.
- docs: Refreshed architecture/detail design status and guide/skill wording so
  the placed first slice is documented as implemented rather than pending final
  selection.
- verify: Re-ran focused current-state gates. `wm_text_access_mcp_spec.spl`
  passes 15/15; touched common UI/MCP files check clean; `check src/compiler`,
  `check src/lib`, `check src/app/mcp`, and `check src/app/simple_lsp_mcp` pass;
  MCP stdio integration passes 5/5; `check-mcp-native-smoke.shs` reports valid
  MCP/LSP tool JSON/schema; `doc/06_spec` executable spec count is 0.
- impl: Added live scalar-payload MCP facade tools:
  `play_wm_text_snapshot`, `play_wm_text_find`, and `play_wm_text_act`. They
  normalize TRACE32, Simple UI, or host WM payloads and call the shared
  `win_text_*` snapshot/query/action core.
- test: Extended the system spec to 17 examples covering static MCP discovery,
  tool-table registration, dispatch wiring, and shared-core use for the live
  facade tools. Directly importing the MCP play handler module from the spec
  caused an interpreter hang after loading `main_lazy_json`; keep that as a
  concrete follow-up for direct handler unit coverage instead of hiding it.
- impl: Added CLI planner/discovery names `simple play wm-text-snapshot`,
  `simple play wm-text-find`, and `simple play wm-text-act`; normalized the
  parser-sensitive play CLI predicate helpers to explicit returns.
- verify: Focused check for touched MCP/play/spec files passed; WM text-access
  system spec passes 18/18; `check src/compiler`, `check src/lib`,
  `check src/app/mcp`, and `check src/app/simple_lsp_mcp` pass; MCP stdio
  integration passes 5/5; native MCP smoke reports valid MCP/LSP schema JSON;
  `doc/06_spec` executable spec count is 0.
- impl: Registered `play` in the native Rust driver, allowed
  `src/app/play/main.spl` dispatch, normalized leading `play` in the Play CLI,
  and kept the Simple/Rust CLI source contracts covered by the system spec.
- verify: Rebuilt the debug native driver and proved
  `simple play wm-text-find trace32 PC --json` reaches the Play planner and
  returns `{"command":"play","status":"planned","subcommand":"wm-text-find","args":2}`.
- verify: Final gates pass: WM text-access system spec 19/19; `check
  src/compiler`, `check src/lib`, `check src/app/mcp`, and `check
  src/app/simple_lsp_mcp`; MCP stdio integration 5/5; native MCP smoke
  JSON/schema checks; Rust `cargo build -p simple-driver`; and `doc/06_spec`
  executable spec count is 0.
- fix: `bin/simple_mcp_server` native `tools/list` was stale and the rebuilt
  native binary segfaulted, so the wrapper now falls back to the source MCP
  entrypoint for stale `tools/list` output and `play_wm_text_*` calls.
  `scripts/setup/setup.sh` generates the same fallback wrapper.
- verify: `scripts/check/check-mcp-native-smoke.shs` now asserts
  `mcp_wm_text_tools_present=true`; wrapper probes show 151 tools and
  `play_wm_text_status`, `play_wm_text_snapshot`, `play_wm_text_find`, and
  `play_wm_text_act` present with clean stderr.
