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
- dev: PASS `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --clean` (1 scenario).
- dev: PASS `SIMPLE_LIB=src bin/simple test test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.spl --mode=interpreter --clean` (103 scenarios).
- dev: Regenerated `doc/06_spec/unit/lib/common/web/browser_session_fetch_wasm_chain_spec.md` and `doc/06_spec/system/app/browser/feature/webgpu_js_wasm_simple_spec.md` with `bin/simple spipe-docgen`; command completed with existing compiler/docgen warnings.
- dev: Strengthened Node-compatible smoke package hardening detection for file (`fs.readFile`, `fs.writeFile`, `fs.promises`, `node:fs`), network (`net.connect`, `tls.connect`, `http.request`, `https.request`), process (`child_process.spawn`), and credential/environment (`process.env`, `Deno.env`, credential handles, API key tokens) escape signatures.
- dev: PASS `SIMPLE_LIB=src bin/simple test test/03_system/os/simpleos_ai_cli_js_node_port_spec.spl --mode=interpreter --clean` (18 scenarios).
- dev: Regenerated `doc/06_spec/system/os/simpleos_ai_cli_js_node_port_spec.md` with `bin/simple spipe-docgen --no-index`; command completed with existing compiler/docgen warnings.
- dev: Updated `doc/03_plan/sys_test/webgpu_js_wasm_simple.md` so REQ-WGPU-006/007 reflect the implemented BrowserSession `fetch` -> `arrayBuffer` -> `WebAssembly.instantiate` path and keep direct WASM-to-WebGPU host bindings as the remaining bridge layer.
- dev: Added deterministic Node-style permission flags from `AiCliManifest` grants (`--experimental-permission`, fs read/write, child process, network, env/credential handles) and embedded them in staged package manifest/launcher marker output. Deny-all manifests now emit only the base permission flag.
- dev: PASS `SIMPLE_LIB=src bin/simple check src/os/ai_cli_js_node_contract.spl`.
- dev: PASS `SIMPLE_LIB=src bin/simple test test/03_system/os/simpleos_ai_cli_js_node_port_spec.spl --mode=interpreter --clean` (20 scenarios).
- dev: Regenerated `doc/06_spec/system/os/simpleos_ai_cli_js_node_port_spec.md` with permission-flag coverage; command completed with existing compiler/docgen warnings.
- dev: PASS `SIMPLE_LIB=src bin/simple test test/03_system/feature/js/node_api_conformance_spec.spl --mode=interpreter --clean` (142 scenarios), covering executable Node-compatible positive APIs plus fail-closed file, process, network, credential/environment, crypto entropy, readline, HTTP/HTTPS, Buffer, EventEmitter, path, process, and OS behavior.
- dev: Regenerated `doc/06_spec/feature/js/node_api_conformance_spec.md`; command completed with existing compiler/docgen warnings.
- dev: Marked the Phase 5 denial-path test checklist item complete in `doc/03_plan/simpleos_nodejs_ai_cli_migration.md` based on the passing system OS contract and executable Node API conformance suites.
- dev: Added the JS/WASM browser bridge slice: the browser system spec now proves `fetch` -> `arrayBuffer` -> `WebAssembly.instantiate` reaches WebGPU global metadata, same-session `navigator.gpu.requestAdapter()` resolves deterministic software-adapter metadata, and a declared WASM import `webgpu.requestAdapter` invokes a JS host callback with `true:webgpu:requestAdapter:function:instantiated:0:7:1`.
- dev: `simple_browser_wasm_gui_contract()` now allows only the narrow `webgpu.requestAdapter` bridge token while the OS contract spec denies `webgpu.requestDevice`, `webgpu.queue.submit`, and `navigator.gpu` direct imports.
- dev: PASS `SIMPLE_LIB=src bin/simple test test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.spl --mode=interpreter --clean` (105 scenarios).
- dev: PASS `SIMPLE_LIB=src bin/simple test test/03_system/os/simpleos_ai_cli_js_node_port_spec.spl --mode=interpreter --clean` (20 scenarios).
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
- dev: PASS `SIMPLE_LIB=src bin/simple test test/03_system/app/browser/feature/webgpu_js_wasm_simple_spec.spl --mode=interpreter --clean` (106 scenarios) and `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl --mode=interpreter --clean` (1 scenario).
- dev: Regenerated `doc/06_spec/system/app/browser/feature/webgpu_js_wasm_simple_spec.md`; command completed with existing compiler/docgen warnings and emitted a stub-style manual.
- dev: Wired Node-compatible credential grants into the JS runtime `process.env` surface. `JsRuntime.grant_node_credential("openai-api-key", value)` exposes only `OPENAI_API_KEY`, keeps ambient keys like `PATH` and undeclared provider keys undefined, and works through both global `process.env` and `require('process').env`.
- dev: Initial Node-compatible credential grant attempts exposed Simple `self`/constructor-context errors in a test helper path; the final implementation uses the existing public `JsRuntime.grant_node_credential(...)` API and avoids direct test mutation of interpreter internals.
- dev: PASS `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/js/engine/interpreter.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/runtime.spl test/03_system/feature/js/node_api_conformance_spec.spl`.
- dev: PASS `SIMPLE_LIB=src bin/simple test test/03_system/feature/js/node_api_conformance_spec.spl --mode=interpreter --clean` (143 scenarios).
- dev: PASS `SIMPLE_LIB=src bin/simple test test/03_system/os/simpleos_ai_cli_js_node_port_spec.spl --mode=interpreter --clean` (25 scenarios).
- dev: Regenerated `doc/06_spec/feature/js/node_api_conformance_spec.md`; docgen completed with existing compiler/docgen warnings and emitted a stub-style manual.
- dev: Marked the Phase 5 credential hardening checklist item complete for the Node-compatible JS runtime credential/env boundary.
- dev: Wired native Node-compatible `child_process.spawn` enforcement to generic sanitized per-command process grant markers, matching `JsRuntime.grant_node_process(...)` instead of hardcoding only the `node` command.
- dev: PASS `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/runtime.spl test/03_system/feature/js/node_api_conformance_spec.spl`.
- dev: PASS `SIMPLE_LIB=src bin/simple test test/03_system/feature/js/node_api_conformance_spec.spl --mode=interpreter --clean` (149 scenarios), including positive `git` spawn only when `git` is explicitly granted and denial when only `node` is granted.
- dev: PASS cross-lane smoke checks: WebGPU JS/WASM Simple (106 scenarios), interpreter perf (10 scenarios), and `scripts/check/check-gtk-gui-repeat-evidence.shs` with deterministic vector checksum 212444.
- dev: Optimized Node-compatible `require()` with a single-entry canonical last-hit cache before the reverse scan over cached module names. Repeated `require('path')`/`require('node:path')` calls now avoid the linear scan while preserving the shared module object.
- dev: PASS `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/js/engine/interpreter.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/03_system/feature/js/node_api_conformance_spec.spl`.
- dev: PASS `SIMPLE_LIB=src bin/simple test test/03_system/feature/js/node_api_conformance_spec.spl --mode=interpreter --clean` (150 scenarios).
- dev: Regenerated `doc/06_spec/feature/js/node_api_conformance_spec.md`; docgen completed with existing compiler/docgen warnings and emitted a stub-style manual.
- dev: PASS cross-lane smoke checks: WebGPU JS/WASM Simple (106 scenarios), interpreter perf (10 scenarios), and `scripts/check/check-gtk-gui-repeat-evidence.shs` with Simple open 224 us, GTK open 75025 us, Simple frame 1 us, GTK frame 27 us, vector checksum 212444 deterministic true.
- dev: Added `scripts/check/check-ai-cli-qemu-lanes.shs`, a contract-first Phase 6
  harness that derives required QEMU serial markers from
  `src/os/ai_cli_js_node_contract.spl`, supports a CI-safe `--contract-only`
  mode, and fails default validation until staged runtime artifacts and real
  guest serial logs exist. Fixed the AI CLI QEMU marker contract so manifest,
  blocker, and blocker-report markers are non-empty in generated lane evidence.
- dev: Added host-side AI CLI smoke package materialization with
  `scripts/check/check-ai-cli-qemu-lanes.shs --stage-smoke-package`. The mode writes
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
- dev: PASS `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/js/engine/interpreter_string_methods.spl src/lib/gc_async_mut/js/engine/interpreter_string_methods.spl src/lib/nogc_async_mut/js/engine/interpreter_string_methods.spl test/03_system/feature/js/node_api_conformance_spec.spl test/03_system/feature/js/es5_conformance_spec.spl`.
- dev: PASS `SIMPLE_LIB=src bin/simple test test/03_system/feature/js/node_api_conformance_spec.spl --mode=interpreter --clean` (151 scenarios), including prefix/suffix coverage through the runtime helper. ES5 conformance remains a pre-existing interpreter-harness failure at 54/54 scenarios returning `nil`.
- dev: PASS cross-lane smoke checks: WebGPU JS/WASM Simple (106 scenarios),
  interpreter perf (10 scenarios), and `scripts/check/check-gtk-gui-repeat-evidence.shs`
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
- dev: Added OS process-boundary AI CLI process grant enforcement for exec,
  spawn_binary, and direct spawn paths. `syscall_spec.spl` covers allowed
  `/usr/bin/git`, denied `/bin/sh`, denied legacy sentinel spawn, and denied
  exec image replacement before executable resolution.
- dev: Added POSIX socket-boundary AI CLI network grant enforcement for
  connect, bind, and listen. `socket_compat_spec.spl` proves ungranted
  endpoints are denied with `-EACCES` before netstack IPC.
- dev: Reconciled WebGPU JS/WASM system-test planning with current executable
  coverage. Full WASM-originated WebGPU ABI, hardware/driver WebGPU execution,
  CTS conformance, and pixel-stable hardware rendering are explicitly follow-up
  scope outside this hardening goal.
- dev: Split real Phase 6 QEMU guest validation into
  `doc/03_plan/agent_tasks/ai_cli_qemu_guest_validation_followup.md` after
  fresh harness evidence showed contract and host staging pass but default
  validation still lacks real guest serial logs.
- dev: Added a focused BrowserSession primitive controls slice for browser
  home and favorite-link state. `BrowserSession` now stores a normalized
  `home_url`, supports `set_home_url`/`go_home`, and can add/update/remove
  favorite links without nested sibling-method dispatch. PASS
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_controls_spec.spl --mode=interpreter --clean`
  (2 scenarios). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_controls_spec.md`.
- dev: Added an RFC 9110 BrowserSession HTTP status semantics slice. Red test
  first failed for unknown valid status-code class fallback and invalid status
  processing; implementation now maps unknown valid codes to their x00 class
  reason phrase and invalid codes to server-error semantics across
  `gc_async_mut`, `nogc_async_mut`, and `nogc_sync_mut` HTTP status utilities.
  PASS `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/http/types.spl src/lib/nogc_async_mut/http/types.spl src/lib/nogc_sync_mut/http/types.spl test/01_unit/lib/common/web/browser_session_http_status_spec.spl`.
  PASS `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_http_status_spec.spl --mode=interpreter --clean`
  (2 scenarios). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_http_status_spec.md`.
- dev: Added the first HTML standard tag base-coverage slice. The red run
  exposed that repeated full renders made the spec take 85s and that
  `<template>` contents were visible in BrowserSession body rendering. The spec
  now covers sectioning/landmark tags (`main`, `section`, `article`, `nav`,
  `header`, `footer`, `aside`, `search`) plus one combined render check, and
  verifies `<template>` source preservation with inert visible rendering.
  `browser_session_html.strip_template_blocks` is now applied during
  BrowserSession visible body extraction while leaving `source_html` intact.
  PASS `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/web/browser_session_html.spl src/lib/gc_async_mut/web/browser_session_runtime.spl test/01_unit/lib/common/web/browser_session_html_tag_std_spec.spl`.
  PASS `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_html_tag_std_spec.spl --mode=interpreter --clean`
  (2 scenarios, 12s after removing repeated renders). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_html_tag_std_spec.md`.
- dev: Added a BrowserSession textual UI-access system slice for primitive
  browser controls. `browser_session_ui_access.spl` exposes back, forward,
  stop, home, favorite, address, and title nodes through `UiAccessSnapshot` and
  routes click actions back into BrowserSession state. PASS
  `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/web/browser_session_ui_access.spl test/03_system/app/browser/feature/browser_session_ui_access_controls_spec.spl`.
  PASS `SIMPLE_LIB=src bin/simple test test/03_system/app/browser/feature/browser_session_ui_access_controls_spec.spl --mode=interpreter --clean`
  (3 scenarios). Regenerated
  `doc/06_spec/03_system/app/browser/feature/browser_session_ui_access_controls_spec.md`.
- dev: Added an HTML scripting tag semantics slice for `script`/`noscript`.
  The first stricter red case proved `noscript` fallback was visible when
  BrowserSession runtime was enabled but no script executed. Implementation now
  strips `noscript` blocks from visible body extraction only when
  `runtime_enabled` is true, while preserving `noscript` fallback when
  `BrowserSession.new_without_runtime()` ignores scripts. PASS
  `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/web/browser_session_html.spl src/lib/gc_async_mut/web/browser_session_runtime.spl test/01_unit/lib/common/web/browser_session_html_scripting_tags_spec.spl`.
  PASS `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_html_scripting_tags_spec.spl --mode=interpreter --clean`
  (3 scenarios). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_html_scripting_tags_spec.md`.
- dev: Added an HTML text-level tag semantics slice. The red run proved
  `html_to_text` preserved normal inline text-level content but collapsed
  `<br>` instead of producing a visible line break. Implementation now extracts
  tag names while stripping markup and maps `br` to `\n`; `wbr` remains an
  optional zero-width break. PASS
  `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/web/browser_session_html.spl test/01_unit/lib/common/web/browser_session_html_text_level_tags_spec.spl`.
  PASS `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_html_text_level_tags_spec.spl --mode=interpreter --clean`
  (2 scenarios). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_html_text_level_tags_spec.md`.
- dev: Added an HTML embedded tag text-alternative slice. The red run proved
  `html_to_text` did not expose `img alt` or `area alt` text. Implementation
  now emits non-empty `alt` text for non-closing `img` and `area` tags while
  preserving ordinary fallback text inside `iframe`, `object`, `video`, and
  `audio`. PASS
  `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/web/browser_session_html.spl test/01_unit/lib/common/web/browser_session_html_embedded_tags_spec.spl`.
  PASS `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_html_embedded_tags_spec.spl --mode=interpreter --clean`
  (2 scenarios). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_html_embedded_tags_spec.md`.
- dev: Added an HTML form/control tag text slice. The red run proved
  `html_to_text` preserved ordinary form container text but dropped
  value-bearing controls. Implementation now emits `input value` and
  `progress`/`meter` value summaries (`value/max` when both are present).
  PASS `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/web/browser_session_html.spl test/01_unit/lib/common/web/browser_session_html_form_tags_spec.spl`.
  PASS `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_html_form_tags_spec.spl --mode=interpreter --clean`
  (2 scenarios). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_html_form_tags_spec.md`.
- dev: Added an HTML table tag text slice. The red run proved table text
  collapsed caption, headers, cells, and rows into one flat string. The helper
  now inserts newlines at table row starts and tabs between `th`/`td` cells.
  PASS `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/web/browser_session_html.spl test/01_unit/lib/common/web/browser_session_html_table_tags_spec.spl`.
  PASS `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_html_table_tags_spec.spl --mode=interpreter --clean`
  (1 scenario). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_html_table_tags_spec.md`.
- dev: Added an HTML grouping/list tag text slice. The red run proved
  paragraph/block grouping, list items, and definition lists collapsed without
  semantic separators. The helper now maps `hr` to a newline, separates `li`
  and `dt` starts with newlines, and formats `dd` as `dt: dd` text. PASS
  `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/web/browser_session_html.spl test/01_unit/lib/common/web/browser_session_html_grouping_tags_spec.spl`.
  PASS `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_html_grouping_tags_spec.spl --mode=interpreter --clean`
  (3 scenarios). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_html_grouping_tags_spec.md`.
- dev: Added an HTML metadata tag text slice. The red run proved
  `html_to_text` leaked document `head`, `title`, and `style` contents into
  visible text. The helper now suppresses text inside `head`, `title`, `style`,
  `script`, and `template` until the matching closing tag. PASS
  `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/web/browser_session_html.spl test/01_unit/lib/common/web/browser_session_html_metadata_tags_spec.spl`.
  PASS `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_html_metadata_tags_spec.spl --mode=interpreter --clean`
  (2 scenarios). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_html_metadata_tags_spec.md`.
- dev: Added an HTML section/heading tag text slice. The red run proved
  adjacent `h1`-`h6`, `hgroup`, and `address` text collapsed into one token.
  The helper now applies line boundaries before and after section text block
  tags while preserving existing paragraph/list expectations. PASS
  `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/web/browser_session_html.spl test/01_unit/lib/common/web/browser_session_html_section_tags_spec.spl`.
  PASS `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_html_section_tags_spec.spl --mode=interpreter --clean`
  (2 scenarios). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_html_section_tags_spec.md`.
- dev: Added an HTML ruby tag text slice. The red run proved ruby without
  `rp` fallback tags collapsed base text and `rt` annotation text. The helper
  now collects `rt` text as parenthesized annotations and suppresses `rp`
  fallback marker text while ruby handling is active. PASS
  `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/web/browser_session_html.spl test/01_unit/lib/common/web/browser_session_html_ruby_tags_spec.spl`.
  PASS `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_html_ruby_tags_spec.spl --mode=interpreter --clean`
  (2 scenarios). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_html_ruby_tags_spec.md`.
- dev: Added an HTML edit tag text slice. The red run proved `ins`/`del`
  text lost revision semantics in plain text extraction. The helper now buffers
  edit text, ignores nested inline markup structurally, and emits `[+...]` for
  inserted text plus `[-...]` for deleted text. PASS
  `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/web/browser_session_html.spl test/01_unit/lib/common/web/browser_session_html_edit_tags_spec.spl`.
  PASS `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_html_edit_tags_spec.spl --mode=interpreter --clean`
  (2 scenarios). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_html_edit_tags_spec.md`.
- dev: Added a real red HTML anchor/UI access navigation scenario and stopped
  before implementation per user instruction. The scenario expects anchors to
  appear as textual UI `link` nodes with resolved `href` metadata and expects
  clicking that link to navigate through BrowserSession resource loading. RED
  `SIMPLE_LIB=src bin/simple test test/03_system/app/browser/feature/browser_session_ui_access_controls_spec.spl --mode=interpreter --clean`
  currently passes 3 existing scenarios and fails the new anchor scenario.
- dev: Replaced the stale interactive-tag placeholder manual with a real
  executable spec using concrete assertions for `details`, `summary`, and
  `dialog` text semantics. No implementation logic was added per the
  stop-before-impl instruction because existing behavior already satisfies the
  selected assertions. PASS
  `SIMPLE_LIB=src bin/simple check test/01_unit/lib/common/web/browser_session_html_interactive_tags_spec.spl`.
  PASS
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_html_interactive_tags_spec.spl --mode=interpreter --clean --json`
  (2 scenarios). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_html_interactive_tags_spec.md`.
- dev: Converted `browser_session_storage_spec.spl` placeholder failure
  branches from `expect(false).to_equal(true)` to explicit real-test failure
  messages for storage method/key collision behavior. No implementation logic
  was added per the stop-before-impl instruction. PASS
  `SIMPLE_LIB=src bin/simple check test/01_unit/lib/common/web/browser_session_storage_spec.spl`.
  RED
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_storage_spec.spl --mode=interpreter --clean --json`
  (0 listed, 0 passed, 1 failed file). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_storage_spec.md`; focused
  placeholder scan reports 0 matches in the storage spec and generated manual.
- dev: Converted `simple_browser_page_spec.spl` missing-target placeholder
  branches from `expect(false).to_equal(true)` to explicit real-test failure
  messages for rendered anchor/form targets, GET/POST submission targets, and
  hit-test resolution. No implementation logic was added per the
  stop-before-impl instruction. PASS
  `SIMPLE_LIB=src bin/simple check test/01_unit/lib/common/web/simple_browser_page_spec.spl`.
  RED
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/simple_browser_page_spec.spl --mode=interpreter --clean --json`
  (0 listed, 0 passed, 4 failed scenarios/files as reported by the runner).
  Regenerated `doc/06_spec/01_unit/lib/common/web/simple_browser_page_spec.md`;
  focused placeholder scan reports 0 matches in the page spec and generated
  manual.
- dev: Converted the first `browser_session_spec.spl` lifecycle slice from
  `expect(false).to_equal(true)` placeholders to explicit real-test failure
  messages for `about:blank` success, stopped navigation rejection, and
  network-navigation rejection. No implementation logic was added per the
  stop-before-impl instruction. PASS
  `SIMPLE_LIB=src bin/simple check test/01_unit/lib/common/web/browser_session_spec.spl`.
  RED
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_spec.spl --mode=interpreter --clean --json`
  (39 passed, 13 failed across the broader legacy file). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_spec.md`; focused
  lifecycle range placeholder scan reports 0 matches, with 81 remaining
  placeholder assertions elsewhere in the same legacy spec.
- dev: Converted the next `browser_session_spec.spl` page-loading slice from
  `expect(false).to_equal(true)` placeholders to explicit real-test failure
  messages for title/body extraction, inline scripts, zero-delay timers,
  external scripts, inline/linked/imported stylesheets, and external module
  graph loading. No implementation logic was added per the stop-before-impl
  instruction. PASS
  `SIMPLE_LIB=src bin/simple check test/01_unit/lib/common/web/browser_session_spec.spl`.
  RED
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_spec.spl --mode=interpreter --clean --json`
  (39 passed, 13 failed across the broader legacy file). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_spec.md`; focused
  page-loading range placeholder scan reports 0 matches, with 73 remaining
  placeholder assertions elsewhere in the same legacy spec.
- dev: Converted the next `browser_session_spec.spl` module/export slice from
  `expect(false).to_equal(true)` placeholders to explicit real-test failure
  messages for inline module default/namespace imports, default class exports,
  named/default re-exports, export-star behavior, namespace re-exports, and
  multi-declarator variable exports. No implementation logic was added per the
  stop-before-impl instruction. PASS
  `SIMPLE_LIB=src bin/simple check test/01_unit/lib/common/web/browser_session_spec.spl`.
  RED
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_spec.spl --mode=interpreter --clean --json`
  (39 passed, 13 failed across the broader legacy file). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_spec.md`; focused
  module/export range placeholder scan reports 0 matches, with 63 remaining
  placeholder assertions elsewhere in the same legacy spec.
- dev: Converted the next `browser_session_spec.spl` module/script follow-up
  slice from `expect(false).to_equal(true)` placeholders to explicit real-test
  failure messages for repeated namespace/default re-export cases, async/defer
  classic script ordering, and deterministic no-runtime document loading. No
  implementation logic was added per the stop-before-impl instruction. PASS
  `SIMPLE_LIB=src bin/simple check test/01_unit/lib/common/web/browser_session_spec.spl`.
  RED
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_spec.spl --mode=interpreter --clean --json`
  (39 passed, 13 failed across the broader legacy file). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_spec.md`; focused
  follow-up range placeholder scan reports 0 matches, with 58 remaining
  placeholder assertions elsewhere in the same legacy spec.
- dev: Converted the next `browser_session_spec.spl` globals/location slice
  from `expect(false).to_equal(true)` placeholders to explicit real-test
  failure messages for browser-like globals, navigator fields, document URL and
  ready state, full location URL parts, `location.href` mutation,
  `location.assign`, and `location.replace` history behavior. No implementation
  logic was added per the stop-before-impl instruction. PASS
  `SIMPLE_LIB=src bin/simple check test/01_unit/lib/common/web/browser_session_spec.spl`.
  RED
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_spec.spl --mode=interpreter --clean --json`
  (39 passed, 13 failed across the broader legacy file). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_spec.md`; focused
  globals/location range placeholder scan reports 0 matches, with 42 remaining
  placeholder assertions elsewhere in the same legacy spec.
- dev: Converted the next `browser_session_spec.spl`
  history/WebGPU/eval/storage slice from `expect(false).to_equal(true)`
  placeholders to explicit real-test failure messages for `history.pushState`,
  `history.replaceState`, secure/insecure WebGPU globals, eval-script document
  mutation sync, and storage/cookie persistence across page loads. No
  implementation logic was added per the stop-before-impl instruction. PASS
  `SIMPLE_LIB=src bin/simple check test/01_unit/lib/common/web/browser_session_spec.spl`.
  RED
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_spec.spl --mode=interpreter --clean --json`
  (39 passed, 13 failed across the broader legacy file). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_spec.md`; focused
  history/WebGPU/eval/storage range placeholder scan reports 0 matches, with 26
  remaining placeholder assertions elsewhere in the same legacy spec.
- dev: Converted the final `browser_session_spec.spl` cookie/fetch/storage/
  history tail slice from `expect(false).to_equal(true)` placeholders to
  explicit real-test failure messages for cookie attribute/removal behavior,
  promise/fetch response settlement, blob metadata/text, transport rejection,
  script-owned location navigation, Storage method compatibility, and
  back/forward/reload. No implementation logic was added per the
  stop-before-impl instruction. PASS
  `SIMPLE_LIB=src bin/simple check test/01_unit/lib/common/web/browser_session_spec.spl`.
  RED
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_spec.spl --mode=interpreter --clean --json`
  (39 passed, 13 failed across the broader legacy file). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_spec.md`; full source
  placeholder scan reports 0 matches in `browser_session_spec.spl`.
- dev: Converted the first `browser_session_async_spec.spl` promise/fetch
  response slice from `expect(false).to_equal(true)` placeholders to explicit
  real-test failure messages for promise adoption/rejection, Promise globals,
  pending fetch settlement, HTTP error response metadata/status text, response
  text/json/body consumption, and fetch request header serialization. No
  implementation logic was added per the stop-before-impl instruction. PASS
  `SIMPLE_LIB=src bin/simple check test/01_unit/lib/common/web/browser_session_async_spec.spl`.
  RED
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_async_spec.spl --mode=interpreter --clean --json`
  (0 passed, 17 failed across the broader async file). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_async_spec.md`; focused
  first async range placeholder scan reports 0 matches, with 22 remaining
  placeholder assertions elsewhere in the same async spec.
- dev: Converted the final `browser_session_async_spec.spl` chained-fetch/
  finally slice from `expect(false).to_equal(true)` placeholders to explicit
  real-test failure messages for chained fetch cookie propagation, Set-Cookie
  filtering, out-of-order response settlement, and fulfilled/rejected
  `Promise.finally` chains. No implementation logic was added per the
  stop-before-impl instruction. PASS
  `SIMPLE_LIB=src bin/simple check test/01_unit/lib/common/web/browser_session_async_spec.spl`.
  RED
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_async_spec.spl --mode=interpreter --clean --json`
  (0 passed, 17 failed across real assertions/failures). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_async_spec.md`; full
  source placeholder scan reports 0 matches in
  `browser_session_async_spec.spl`.
- dev: Added a real red JS/WASM/HTTP standard case for
  `WebAssembly.compileStreaming(window.fetch(...))` MIME enforcement. The test
  commits a valid WASM payload with `Content-Type: text/plain` and expects
  rejection as `unsupported-wasm-content-type:text/plain`, proving content-type
  validation rather than byte validation alone. No implementation logic was
  added per the stop-before-impl instruction. PASS
  `SIMPLE_LIB=src bin/simple check test/01_unit/lib/common/web/browser_session_async_spec.spl`.
  RED
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_async_spec.spl --mode=interpreter --clean --json`
  (0 passed, 18 failed across real assertions/failures). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_async_spec.md`; full
  source placeholder scan reports 0 matches.
- dev: Added a paired real red JS/WASM/HTTP standard case for
  `WebAssembly.instantiateStreaming(window.fetch(...))` MIME enforcement. The
  test commits a valid WASM payload with `Content-Type: text/plain` and expects
  rejection as `unsupported-wasm-content-type:text/plain`, covering the
  instantiation streaming path separately from compile streaming. No
  implementation logic was added per the stop-before-impl instruction. PASS
  `SIMPLE_LIB=src bin/simple check test/01_unit/lib/common/web/browser_session_async_spec.spl`.
  RED
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_async_spec.spl --mode=interpreter --clean --json`
  (0 passed, 19 failed across real assertions/failures). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_async_spec.md`; full
  source placeholder scan reports 0 matches.
- dev: Added a real red HTTP/JS browser standard case for same-origin fetch
  redirect following. `browser_session_http_status_spec.spl` now requires a
  `302 Location: /new` response to queue a redirected `GET` request and resolve
  the page script only after the final `200` body, covering `HTTP-STATUS-3XX-001`
  without adding BrowserSession implementation logic. PASS
  `SIMPLE_LIB=src bin/simple check test/01_unit/lib/common/web/browser_session_http_status_spec.spl`.
  RED
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_http_status_spec.spl --mode=interpreter --clean --json`
  (2 passed, 1 failed). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_http_status_spec.md`;
  source placeholder scan reports 0 matches.
- dev: Added a real red HTTP/JS browser standard case for `HEAD` fetch response
  body semantics. The spec now requires the pending request to preserve
  `method: HEAD` and requires `Response.text()` to expose an empty body even
  when the committed response carries bytes, covering `HTTP-METHOD-HEAD-001`
  without adding BrowserSession implementation logic. PASS
  `SIMPLE_LIB=src bin/simple check test/01_unit/lib/common/web/browser_session_http_status_spec.spl`.
  RED
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_http_status_spec.spl --mode=interpreter --clean --json`
  (2 passed, 2 failed). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_http_status_spec.md`;
  source placeholder scan reports 0 matches.
- dev: Added a real red HTTP/JS browser standard case for `303 See Other`
  redirect method rewriting. The spec now requires a `POST` fetch with body to
  queue the redirected `Location` request as `GET` with an empty body and resolve
  the page script from the final response, covering fetch redirect/method
  semantics without adding BrowserSession implementation logic. PASS
  `SIMPLE_LIB=src bin/simple check test/01_unit/lib/common/web/browser_session_http_status_spec.spl`.
  RED
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_http_status_spec.spl --mode=interpreter --clean --json`
  (2 passed, 3 failed). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_http_status_spec.md`;
  source placeholder scan reports 0 matches.
- dev: Added a real red HTTP/JS browser standard case for `307 Temporary
  Redirect` method/body preservation. The spec now requires a `POST` fetch with
  body to queue the redirected `Location` request as `POST` with the original
  body intact and resolve page JavaScript from the final response, covering
  fetch redirect preservation semantics without adding BrowserSession
  implementation logic. PASS
  `SIMPLE_LIB=src bin/simple check test/01_unit/lib/common/web/browser_session_http_status_spec.spl`.
  RED
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_http_status_spec.spl --mode=interpreter --clean --json`
  (2 passed, 4 failed). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_http_status_spec.md`;
  source placeholder scan reports 0 matches.
- dev: Added a real red HTTP/JS browser standard case for `308 Permanent
  Redirect` method/body preservation. The spec now requires a `POST` fetch with
  body to queue the redirected `Location` request as `POST` with the original
  body intact and resolve page JavaScript from the final response, covering the
  permanent redirect preservation counterpart to the 307 case without adding
  BrowserSession implementation logic. PASS
  `SIMPLE_LIB=src bin/simple check test/01_unit/lib/common/web/browser_session_http_status_spec.spl`.
  RED
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_http_status_spec.spl --mode=interpreter --clean --json`
  (2 passed, 5 failed). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_http_status_spec.md`;
  source placeholder scan reports 0 matches.
- dev: Added a real red HTTPS/JS browser standard case for active mixed-content
  fetch blocking. The spec now requires an HTTPS page to reject
  `fetch("http://example.com/insecure.txt")` before any network request is
  queued and to expose the mixed-content rejection to page JavaScript, covering
  `HTTPS-SECURE-CONTEXT-001` without adding BrowserSession implementation
  logic. PASS
  `SIMPLE_LIB=src bin/simple check test/01_unit/lib/common/web/browser_session_http_status_spec.spl`.
  RED
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_http_status_spec.spl --mode=interpreter --clean --json`
  (2 passed, 6 failed). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_http_status_spec.md`;
  source placeholder scan reports 0 matches.
- dev: Added a real red JS/WASM/HTTPS browser standard case for active
  mixed-content WASM streaming fetch blocking. The async spec now requires
  `WebAssembly.compileStreaming(fetch("http://example.com/module.wasm"))` from
  an HTTPS page to reject as mixed content before any network request is queued,
  covering `HTTPS-FETCH-WASM-001` without adding BrowserSession implementation
  logic. PASS
  `SIMPLE_LIB=src bin/simple check test/01_unit/lib/common/web/browser_session_async_spec.spl`.
  RED
  `SIMPLE_LIB=src bin/simple test test/01_unit/lib/common/web/browser_session_async_spec.spl --mode=interpreter --clean --json`
  (0 passed, 20 failed). Regenerated
  `doc/06_spec/01_unit/lib/common/web/browser_session_async_spec.md`; source
  placeholder scan reports 0 matches.
