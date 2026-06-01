# Feature: nodejs-js-wasm-hardening

## Raw Request
$sp_dev  nodejs level js engine and web browser js, wasm hardening

## Task Type
feature

## Refined Goal
Harden the Simple JavaScript runtime so NodeJS-compatible APIs, browser JavaScript, fetch-driven WebAssembly loading, and WebGPU-adjacent WASM execution have explicit capability boundaries and verified positive and denial behavior.

## Acceptance Criteria
- AC-1: NodeJS-compatible JS APIs expose deterministic, fail-closed implementations for file, process, network, credentials/environment, Buffer, EventEmitter, path, OS, crypto, readline, HTTP/HTTPS, and child-process surfaces with tests proving declared behavior and denial behavior.
- AC-2: BrowserSession exposes secure-context browser JavaScript APIs including `fetch`, Promise chaining, response body helpers, WebAssembly constructors/methods, and WebGPU globals without regressing existing page JS execution.
- AC-3: BrowserSession can load a WASM asset through a page or script fetch flow, convert the response body to bytes, instantiate it through `WebAssembly.instantiate`, and expose deterministic module/instance evidence in the same browser session.
- AC-4: WASM compiler target helpers and backend selection use the same authoritative backend type definitions and all WASM compile target-helper assertions pass.
- AC-5: WebGPU JS/WASM system coverage passes for the current software-backed WebGPU API, browser JS globals, WASM host behavior, and WASM asset-loading bridge.
- AC-6: Hardening docs, SPipe scenario specs, and generated `doc/06_spec` manuals describe current behavior accurately, with remaining out-of-scope work explicitly tracked instead of hidden behind stale pending notes.
- AC-7: Focused verification commands for the affected JS engine, BrowserSession, WASM compiler, and WebGPU JS/WASM specs pass or produce documented release-blocking defects with concrete root-cause evidence.

## Scope Exclusions
Full real Node/V8/libuv porting, hardware WebGPU/CTS conformance, and QEMU guest runtime validation remain out of scope unless a focused fix directly requires them.

## Phase
dev-incomplete

## Log
- dev: Created state file with 7 acceptance criteria (type: feature)
- dev: Fixed WASM target-helper import drift and found BrowserSession fetch promise ID parsing bug (`parse_non_negative_i64_text` passed text into integer `_digit_val`).
- dev: Added host Promise methods on pending promises and made WebAssembly indexed payload extraction prefer `byteLength`/`length` before `array_length`.
- dev: Fixed BrowserSession fetch promise-chain execution by carrying handler metadata into promise host objects, reverse-scanning latest promise state/value properties, invoking promise callbacks through the async-safe callback path, and splitting nested native arrayBuffer byte extraction that triggered `self` lookup failures.
- dev: Hardened direct native WebAssembly promise callbacks (`instantiate.then/catch`, no-GC `compile.then/catch`) to use the same promise-safe callback invocation path instead of `_invoke_function`.
- dev: Mirrored host Promise methods and `Response.arrayBuffer` onto `nogc_async_mut` async response/promise objects for runtime-family parity.
- dev: Strengthened browser WASM fetch-chain specs to prove exact queue result, pre-commit emptiness, ordered `fetch>arrayBuffer>instantiate` stages, and fetched-body module metadata (`byteLength`/`sectionCount`).
- dev: PASS `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/js/engine/interpreter.spl src/lib/nogc_sync_mut/js/engine/interpreter_async.spl src/lib/gc_async_mut/js/engine/interpreter_async.spl src/lib/nogc_async_mut/js/engine/interpreter_async.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/gc_async_mut/js/engine/interpreter_native.spl`.
- dev: PASS `SIMPLE_LIB=src bin/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --clean` (1 scenario).
- dev: PASS `SIMPLE_LIB=src bin/simple test test/system/app/browser/feature/webgpu_js_wasm_simple_spec.spl --mode=interpreter --clean` (103 scenarios).
- dev: Regenerated `doc/06_spec/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.md` and `doc/06_spec/system/app/browser/feature/webgpu_js_wasm_simple_spec.md` with `bin/simple spipe-docgen`; command completed with existing compiler/docgen warnings.
- dev: Strengthened Node-compatible smoke package hardening detection for file (`fs.readFile`, `fs.writeFile`, `fs.promises`, `node:fs`), network (`net.connect`, `tls.connect`, `http.request`, `https.request`), process (`child_process.spawn`), and credential/environment (`process.env`, `Deno.env`, credential handles, API key tokens) escape signatures.
- dev: PASS `SIMPLE_LIB=src bin/simple test test/system/os/simpleos_ai_cli_js_node_port_spec.spl --mode=interpreter --clean` (18 scenarios).
- dev: Regenerated `doc/06_spec/system/os/simpleos_ai_cli_js_node_port_spec.md` with `bin/simple spipe-docgen --no-index`; command completed with existing compiler/docgen warnings.
- dev: Updated `doc/03_plan/sys_test/webgpu_js_wasm_simple.md` so REQ-WGPU-006/007 reflect the implemented BrowserSession `fetch` -> `arrayBuffer` -> `WebAssembly.instantiate` path and keep direct WASM-to-WebGPU host bindings as the remaining bridge layer.
- dev: Added deterministic Node-style permission flags from `AiCliManifest` grants (`--experimental-permission`, fs read/write, child process, network, env/credential handles) and embedded them in staged package manifest/launcher marker output. Deny-all manifests now emit only the base permission flag.
- dev: PASS `SIMPLE_LIB=src bin/simple check src/os/ai_cli_js_node_contract.spl`.
- dev: PASS `SIMPLE_LIB=src bin/simple test test/system/os/simpleos_ai_cli_js_node_port_spec.spl --mode=interpreter --clean` (20 scenarios).
- dev: Regenerated `doc/06_spec/system/os/simpleos_ai_cli_js_node_port_spec.md` with permission-flag coverage; command completed with existing compiler/docgen warnings.
- dev: PASS `SIMPLE_LIB=src bin/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --clean` (142 scenarios), covering executable Node-compatible positive APIs plus fail-closed file, process, network, credential/environment, crypto entropy, readline, HTTP/HTTPS, Buffer, EventEmitter, path, process, and OS behavior.
- dev: Regenerated `doc/06_spec/feature/js/node_api_conformance_spec.md`; command completed with existing compiler/docgen warnings.
- dev: Marked the Phase 5 denial-path test checklist item complete in `doc/03_plan/simpleos_nodejs_ai_cli_migration.md` based on the passing system OS contract and executable Node API conformance suites.
- dev: Added the JS/WASM browser bridge slice: the browser system spec now proves `fetch` -> `arrayBuffer` -> `WebAssembly.instantiate` reaches WebGPU global metadata, same-session `navigator.gpu.requestAdapter()` resolves deterministic software-adapter metadata, and a declared WASM import `webgpu.requestAdapter` invokes a JS host callback with `true:webgpu:requestAdapter:function:instantiated:0:7:1`.
- dev: `simple_browser_wasm_gui_contract()` now allows only the narrow `webgpu.requestAdapter` bridge token while the OS contract spec denies `webgpu.requestDevice`, `webgpu.queue.submit`, and `navigator.gpu` direct imports.
- dev: PASS `SIMPLE_LIB=src bin/simple test test/system/app/browser/feature/webgpu_js_wasm_simple_spec.spl --mode=interpreter --clean` (105 scenarios).
- dev: PASS `SIMPLE_LIB=src bin/simple test test/system/os/simpleos_ai_cli_js_node_port_spec.spl --mode=interpreter --clean` (20 scenarios).
- dev: PASS `SIMPLE_LIB=src bin/simple check src/os/ai_cli_js_node_contract.spl`.
- dev: Regenerated `doc/06_spec/system/app/browser/feature/webgpu_js_wasm_simple_spec.md` and `doc/06_spec/system/os/simpleos_ai_cli_js_node_port_spec.md`; command completed with existing compiler/docgen warnings/stub summaries.
- dev: Added executable Deno permission model comparison flags from `AiCliManifest` grants (`--allow-read`, `--allow-write`, `--allow-net`, `--allow-run`, `--allow-env`) and fail-closed deny-all behavior.
- dev: Added explicit serial-marker assertions that QEMU marker fragments and staged launchers include `[ai-cli] hardening:ok app=<tool>`, then marked the Deno comparison and hardening OK marker Phase 5 checklist items complete.
