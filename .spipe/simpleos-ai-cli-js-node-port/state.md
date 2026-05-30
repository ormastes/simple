# Feature: simpleos-ai-cli-js-node-port

## Raw Request
$sp_dev  harden javascript, porting nodejs, port codex, claude, gemini cli on simple os on qemu(riscv/x85/arm)

## Task Type
feature

## Refined Goal
Enable hardened JavaScript/Node.js-compatible execution for Codex, Claude, and Gemini CLI workflows inside SimpleOS QEMU lanes for RISC-V, x86, and ARM targets.

## Acceptance Criteria
- AC-1: The supported JavaScript/Node.js subset for AI CLI execution is documented, including filesystem, process, terminal, network/TLS, timers, module loading, and npm/package assumptions.
- AC-2: SimpleOS exposes or emulates the OS services required by the selected Node.js-compatible CLI runtime with fail-closed capability checks for file, process, network, and credential access.
- AC-3: Codex, Claude, and Gemini CLI launch plans are represented as concrete SimpleOS package/command manifests with declared dependencies and unsupported features called out.
- AC-4: QEMU validation lanes exist for RISC-V, x86, and ARM that can boot SimpleOS, provision the selected JS/Node runtime and one AI CLI smoke command, and capture guest-side serial/log evidence.
- AC-5: The JavaScript runtime hardening path rejects unsafe host escapes, ambient credential reads, unbounded process spawning, and undeclared network access; focused tests cover each denial.
- AC-6: Focused SPipe specs and generated scenario manuals cover the happy path and hardening denial paths without placeholder passes.
- AC-7: If full CLI execution remains blocked, the blockers are documented with evidence, owner files, and the next smallest implementation step.

## Scope Exclusions
Full upstream Node.js parity, real AI service authentication, release tagging, and physical hardware validation are out of scope until the QEMU lanes prove the guest runtime contract.

## Phase
implementation-in-progress

## Log
- dev: Created state file with 7 acceptance criteria (type: feature). Interpreted `x85` as x86 unless corrected by the user.
- research: Added local research, domain research, feature requirement options, and NFR options. Final requirements are pending user option selection.
- design-draft: Added a pre-requirements runtime contract matrix and draft system-test plan without selecting final requirements.
- research: Recorded the explicit user-selection gate in `doc/02_requirements/feature/simpleos_ai_cli_js_node_port_selection_needed.md`; interactive selection prompt was unavailable in the current mode.
- plan: Added `doc/03_plan/agent_tasks/simpleos_ai_cli_js_node_port_traceability_scaffold.md` to map AC-1..AC-7 to pending requirement families and the first post-selection task queue.
- requirements: Final requirements selected as contract-first compatibility layer with security-first/reproducible manifest gates.
- implementation: Added `src/os/ai_cli_js_node_contract.spl` with Codex, Claude, and Gemini smoke manifests, fail-closed grant checks, QEMU marker fragments, RISC-V/x86/ARM lane contracts, serial acceptance, and explicit Node/V8/libuv blocker status.
- verification: Focused SPipe spec `test/system/os/simpleos_ai_cli_js_node_port_spec.spl` passes with 9 scenarios in interpreter mode.
- verification: Re-ran `test/system/os/simpleos_ai_cli_js_node_port_spec.spl --mode=interpreter` after shared generated-WASM/no-JavaScript web render API hardening; the SimpleOS AI CLI manifest contract still passes.
- research: Checked current Bun documentation for runtime architecture signals: single binary, JavaScriptCore, Zig, built-in package/transpile/bundle/test surfaces, and ongoing Node compatibility; recorded why SimpleOS should copy the cohesive tool shape but keep a Simple MDSOC+ runtime capsule.
- implementation: Extended the AI CLI JS/Node contract with a Bun-informed Simple JS runtime profile plus a Simple browser generated-WASM GUI contract covering target matrix, allowed imports, denied host escapes, required exports, and browser/QEMU evidence markers.
- verification: `SIMPLE_LIB=src bin/simple check src/os/ai_cli_js_node_contract.spl test/system/os/simpleos_ai_cli_js_node_port_spec.spl` passes; `SIMPLE_LIB=src bin/simple test test/system/os/simpleos_ai_cli_js_node_port_spec.spl --mode=interpreter --clean` passes with 14 scenarios; regenerated `doc/06_spec/system/os/simpleos_ai_cli_js_node_port_spec.md` with `bin/simple spipe-docgen`.
- implementation: Mirrored the generated-GUI WASM import/export contract into `common.ui.wasm_hello_gui` with `WasmHelloGuiModuleContractEvidence`, default browser evidence, summary text, and fail-closed rejection for denied or unlisted imports and missing `simple_app_*` exports.
- verification: `SIMPLE_LIB=src bin/simple check src/lib/common/ui/wasm_hello_gui.spl test/unit/lib/common/ui/wasm_hello_gui_spec.spl` passes; `SIMPLE_LIB=src bin/simple test test/unit/lib/common/ui/wasm_hello_gui_spec.spl --mode=interpreter --clean` passes with 17 scenarios; regenerated `doc/06_spec/unit/lib/common/ui/wasm_hello_gui_spec.md`.
- implementation: Hardened `browser_script_execute` by removing the temp-file `bin/simple` subprocess path, adding offset-safe script tag scanning, executing only deterministic literal `console.log(...)` browser JavaScript, and fail-closing Node/host escapes, external scripts, unsupported script types, and network/process/filesystem/env access with diagnostics.
- verification: `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/gpu/browser_engine/browser_script_execute.spl src/lib/gc_async_mut/gpu/browser_engine/browser_script_render.spl test/unit/browser_engine/script/browser_script_execute_spec.spl` passes; `SIMPLE_LIB=src bin/simple test test/unit/browser_engine/script/browser_script_execute_spec.spl --mode=interpreter --clean` passes with 4 scenarios, including renderer-level denial diagnostics; regenerated `doc/06_spec/unit/browser_engine/script/browser_script_execute_spec.md`.
- implementation: Added `AiCliRuntimeSmokePackage` generation for deterministic SimpleOS staged AI CLI smoke package contents: manifest SDN, launcher source, runtime stub source, package index SDN, marker payload, readiness, and source hardening diagnostics.
- verification: `SIMPLE_LIB=src bin/simple check src/os/ai_cli_js_node_contract.spl test/system/os/simpleos_ai_cli_js_node_port_spec.spl` passes; `SIMPLE_LIB=src bin/simple test test/system/os/simpleos_ai_cli_js_node_port_spec.spl --mode=interpreter --clean` passes with 16 scenarios; regenerated `doc/06_spec/system/os/simpleos_ai_cli_js_node_port_spec.md`.

## Current Blocker
Full Codex, Claude, and Gemini execution in SimpleOS QEMU remains blocked until
a Node-compatible runtime artifact is staged in the guest and each RISC-V,
x86, and ARM lane emits the required guest-side runtime and CLI smoke markers.
