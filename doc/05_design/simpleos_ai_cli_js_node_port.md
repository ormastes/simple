<!-- codex-design -->
# Detail Design: SimpleOS AI CLI JS/Node Port

## Data Model

`src/os/ai_cli_js_node_contract.spl` defines `AiCliManifest` with:

- identity: `app_id`, `display_name`;
- runtime: `runtime_kind`, `entry_path`, `args`;
- package pins: `package_id`, `package_version`, `package_checksum`,
  `runtime_artifact`;
- grants: file, process, network, credential, terminal;
- QEMU evidence: marker fragments and unsupported features.

Supported runtime kinds are `node-compatible`, `bundled-node`, and
`simple-js-agent`. Unsupported runtimes fail validation.

The same module now defines:

- `AiCliRuntimeProfile` for the Bun-informed Simple JS runtime shape;
- `AiCliWasmBrowserContract` for generated GUI WASM import/export and browser
  evidence gates.

## Algorithms

- Validation returns an empty string for valid manifests or a deterministic
  reason for the first invalid field.
- Grant checks are fail-closed: empty grants deny access.
- File grants allow exact prefixes; process, network, and credential grants
  allow exact names or `*`.
- Capability summaries are stable text containing identity, runtime, package
  pins, grants, terminal requirement, unsupported features, and QEMU markers.
- Target normalization maps `x85`, `x86`, and `x86_64` to `x86`.
- Runtime profile support checks require the Node-compatible surfaces used by
  AI CLIs, including filesystem, process, TTY, network, TLS, module resolution,
  and WebAssembly.
- WASM browser import checks deny unlisted imports and explicit host escapes.
- WASM browser export checks require init, render, and event entrypoints before
  execution can be claimed.

## Built-In Manifests

Codex, Claude, and Gemini smoke manifests use non-authenticated help/version
style commands and declare credential handles rather than ambient secret reads.
They include package pin fields as `pending` so real bundle identifiers can be
added without changing the contract.

## Bun-Informed Runtime Profile

`bun_informed_simple_js_runtime_profile` records the target Simple runtime
shape: one cohesive developer-facing surface for script execution, package
manifest reading, transpile hooks, bundle planning, and smoke testing. It keeps
the implementation as a Simple MDSOC capsule rather than adopting Bun's
Zig/JavaScriptCore internals.

## Browser/WASM Contract

`simple_browser_wasm_gui_contract` covers Simple browser, host WM, SimpleOS WM,
Android, and iOS. A generated GUI WASM module must use only declared
`simple_ui.*` imports, must not import filesystem/process/env/network/TLS/host
shell escape APIs, and must export `simple_app_init`, `simple_app_render`, and
`simple_app_event`.

The browser-facing implementation mirrors this gate in
`common.ui.wasm_hello_gui` through `WasmHelloGuiModuleContractEvidence`. That
keeps the AI CLI runtime contract and generated-WASM browser artifact evidence
aligned without duplicating separate policy strings in each test.

## Browser Script Execution

`browser_script_execute` is currently a hardened in-process policy layer, not a
full JavaScript VM. It collects `<script>` tags, uses offset-safe scanning, and
executes only literal `console.log(...)` statements. Node-like and host-like
escape surfaces are denied before execution, external script URLs are denied,
and unsupported script types fail closed. The result object reports collected,
executed, and denied script counts plus diagnostics so future browser rendering
and QEMU evidence can prove that no host subprocess fallback was used.

## Error Handling

The first slice avoids `Result` plumbing in callers by returning deterministic
validation text. Empty text means success; any non-empty text is a hard denial.

## Test Coverage

`test/system/os/simpleos_ai_cli_js_node_port_spec.spl` covers:

- manifest fields and built-in constructors;
- deterministic summary and QEMU marker data;
- fail-closed denials for missing file/process/network/credential grants;
- invalid runtime and missing entry rejection;
- `x85` target normalization;
- explicit full Node/V8/libuv blocker declaration;
- Bun-informed runtime profile gates;
- Simple browser generated-WASM import/export denial gates;
- generated-WASM hello GUI import/export evidence in
  `test/unit/lib/common/ui/wasm_hello_gui_spec.spl`;
- hardened browser script execution and denial coverage in
  `test/unit/browser_engine/script/browser_script_execute_spec.spl`.
