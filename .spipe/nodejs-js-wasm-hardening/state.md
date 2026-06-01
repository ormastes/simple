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
- dev: Tightened file grant prefix matching so `/home/user/work` no longer grants `/home/user/workspace`, and added VFS-style file boundary decisions with `allowed`, `file-grant-denied`, and `invalid-path` outcomes. Phase 5 VFS enforcement remains unchecked until this decision path is wired into the actual VFS open/read/write boundary.
- dev: Added socket-style network boundary decisions that normalize `host:port`, reject malformed endpoints, preserve allowlist behavior, and return `network-grant-denied`/`invalid-endpoint` reasons. Phase 5 socket enforcement remains unchecked until this decision path is wired into the actual socket/connect boundary.
- dev: Added process spawn boundary decisions that normalize path-qualified commands to allowlisted executable names, reject shell-style command strings, and return `process-grant-denied`/`invalid-command` reasons. Phase 5 process enforcement remains unchecked until this decision path is wired into the actual spawn/exec boundary.
- dev: Added credential read boundary decisions that normalize declared handles, reject ambient `process.env`/`Deno.env`-style reads, reject inline API-key token shapes, and return `credential-grant-denied`/`ambient-env-denied`/`credential-token-denied` reasons. Phase 5 credential enforcement remains unchecked until this decision path is wired into the actual env/credential read boundary.
- dev: Fixed nested host-Promise assimilation for BrowserSession WebGPU callbacks returned from fetched WASM instantiation chains. `webgpu_js_wasm_simple_spec.spl` now proves `fetch` -> `arrayBuffer` -> `WebAssembly.instantiate` -> `Promise.resolve(navigator.gpu.requestAdapter())` resolves adapter metadata instead of passing an inner promise object downstream.
- dev: PASS `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/js/engine/interpreter_async.spl src/lib/nogc_async_mut/js/engine/interpreter_async.spl src/lib/nogc_sync_mut/js/engine/interpreter_async.spl src/lib/gc_async_mut/js/engine/interpreter_native.spl src/lib/nogc_async_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl`.
- dev: PASS `SIMPLE_LIB=src bin/simple test test/system/app/browser/feature/webgpu_js_wasm_simple_spec.spl --mode=interpreter --clean` (106 scenarios) and `SIMPLE_LIB=src bin/simple test test/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --clean` (1 scenario).
- dev: Regenerated `doc/06_spec/system/app/browser/feature/webgpu_js_wasm_simple_spec.md`; command completed with existing compiler/docgen warnings and emitted a stub-style manual.
- dev: Wired Node-compatible credential grants into the JS runtime `process.env` surface. `JsRuntime.grant_node_credential("openai-api-key", value)` exposes only `OPENAI_API_KEY`, keeps ambient keys like `PATH` and undeclared provider keys undefined, and works through both global `process.env` and `require('process').env`.
- dev: Initial Node-compatible credential grant attempts exposed Simple `self`/constructor-context errors in a test helper path; the final implementation uses the existing public `JsRuntime.grant_node_credential(...)` API and avoids direct test mutation of interpreter internals.
- dev: PASS `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/js/engine/interpreter.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/runtime.spl test/feature/js/node_api_conformance_spec.spl`.
- dev: PASS `SIMPLE_LIB=src bin/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --clean` (143 scenarios).
- dev: PASS `SIMPLE_LIB=src bin/simple test test/system/os/simpleos_ai_cli_js_node_port_spec.spl --mode=interpreter --clean` (25 scenarios).
- dev: Regenerated `doc/06_spec/feature/js/node_api_conformance_spec.md`; docgen completed with existing compiler/docgen warnings and emitted a stub-style manual.
- dev: Marked the Phase 5 credential hardening checklist item complete for the Node-compatible JS runtime credential/env boundary.
- dev: Wired native Node-compatible `child_process.spawn` enforcement to generic sanitized per-command process grant markers, matching `JsRuntime.grant_node_process(...)` instead of hardcoding only the `node` command.
- dev: PASS `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/runtime.spl test/feature/js/node_api_conformance_spec.spl`.
- dev: PASS `SIMPLE_LIB=src bin/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --clean` (149 scenarios), including positive `git` spawn only when `git` is explicitly granted and denial when only `node` is granted.
- dev: PASS cross-lane smoke checks: WebGPU JS/WASM Simple (106 scenarios), interpreter perf (10 scenarios), and `scripts/check-gtk-gui-repeat-evidence.shs` with deterministic vector checksum 212444.
- dev: Optimized Node-compatible `require()` with a single-entry canonical last-hit cache before the reverse scan over cached module names. Repeated `require('path')`/`require('node:path')` calls now avoid the linear scan while preserving the shared module object.
- dev: PASS `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/js/engine/interpreter.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`.
- dev: PASS `SIMPLE_LIB=src bin/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --clean` (150 scenarios).
- dev: Regenerated `doc/06_spec/feature/js/node_api_conformance_spec.md`; docgen completed with existing compiler/docgen warnings and emitted a stub-style manual.
- dev: PASS cross-lane smoke checks: WebGPU JS/WASM Simple (106 scenarios), interpreter perf (10 scenarios), and `scripts/check-gtk-gui-repeat-evidence.shs` with Simple open 224 us, GTK open 75025 us, Simple frame 1 us, GTK frame 27 us, vector checksum 212444 deterministic true.
- dev: Added `scripts/check-ai-cli-qemu-lanes.shs`, a contract-first Phase 6
  harness that derives required QEMU serial markers from
  `src/os/ai_cli_js_node_contract.spl`, supports a CI-safe `--contract-only`
  mode, and fails default validation until staged runtime artifacts and real
  guest serial logs exist. Fixed the AI CLI QEMU marker contract so manifest,
  blocker, and blocker-report markers are non-empty in generated lane evidence.
- dev: Added host-side AI CLI smoke package materialization with
  `scripts/check-ai-cli-qemu-lanes.shs --stage-smoke-package`. The mode writes
  `AI_MANIFEST.SDN`, `launch.spl`, `qemu_markers.txt`, a short package
  manifest, generated `<app>.js` smoke entry, and `runtime.smf` under the
  FAT32-like staging tree while reporting
  `host-package-materialized-no-guest-validation`; default lane validation
  still requires real guest serial logs.
- dev: Added a disk-image import manifest bridge to stage mode. The generated
  `ai-cli-disk-import.tsv` records app, target, guest path, host path, byte
  count, and digest for every staged smoke package file so the next slice can
  ingest the tree into FAT32 tooling without mistaking host staging for QEMU
  guest evidence.
- dev: Added host-side FAT32 ingestion readiness coverage for the AI CLI
  staging layout. `host_fat32_tree_populator_spec.spl` now mirrors
  `sys/runtime/node-compatible/x86/runtime.smf` and `sys/apps/codex/*` into a
  formatted image and verifies the staged runtime, JS entry, manifest, and QEMU
  marker payload bytes are present in the image. This remains host-side
  readiness, not guest serial evidence.
- dev: Optimized JS `String.startsWith` and `String.endsWith` across the
  sync, GC async, and no-GC async interpreter string-method families by routing
  directly through runtime text primitives instead of manual per-character
  loops.
- dev: PASS `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/js/engine/interpreter_string_methods.spl src/lib/gc_async_mut/js/engine/interpreter_string_methods.spl src/lib/nogc_async_mut/js/engine/interpreter_string_methods.spl test/feature/js/node_api_conformance_spec.spl test/feature/js/es5_conformance_spec.spl`.
- dev: PASS `SIMPLE_LIB=src bin/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --clean` (151 scenarios), including prefix/suffix coverage through the runtime helper. ES5 conformance remains a pre-existing interpreter-harness failure at 54/54 scenarios returning `nil`.
- dev: PASS cross-lane smoke checks: WebGPU JS/WASM Simple (106 scenarios),
  interpreter perf (10 scenarios), and `scripts/check-gtk-gui-repeat-evidence.shs`
  with Simple open 210 us, GTK open 77889 us, Simple frame 1 us, GTK frame
  27 us, vector checksum 212444 deterministic true.
- dev: Regenerated `doc/06_spec/feature/js/node_api_conformance_spec.md`;
  docgen completed with existing compiler/docgen warnings and emitted a
  stub-style manual.
- dev: Added a restartable Phase 6 host-image population slice. The AI CLI QEMU
  harness now accepts `--stage-smoke-package --populate-fat32-image <img>` to
  materialize the selected smoke package and mirror it into an existing
  formatted FAT32 image, reporting `fat32_populate_status=host-image-populated`
  only when the populator succeeds. The FAT32 path lookup now resolves its own
  8.3 aliases for long directory names such as `node-compatible` after image
  reloads. This is still host-side image evidence, not QEMU guest validation.
- dev: Added VFS-manager AI CLI file grant enforcement. `VfsManager` can now
  carry an `AiCliManifest` policy and denies ungranted absolute paths,
  sibling-prefix escapes, and relative paths before routing open/stat/readdir,
  directory mutation, rename/symlink, preload, and path-based read/write
  operations. `vfs_spec.spl` covers allowed workspace paths, denied
  `/home/user/workspace` sibling escape, invalid relative paths, rename target
  denial, and clearing the manifest back to unrestricted routing.
