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

## Algorithms

- Validation returns an empty string for valid manifests or a deterministic
  reason for the first invalid field.
- Grant checks are fail-closed: empty grants deny access.
- File grants allow exact prefixes; process, network, and credential grants
  allow exact names or `*`.
- Capability summaries are stable text containing identity, runtime, package
  pins, grants, terminal requirement, unsupported features, and QEMU markers.
- Target normalization maps `x85`, `x86`, and `x86_64` to `x86`.

## Built-In Manifests

Codex, Claude, and Gemini smoke manifests use non-authenticated help/version
style commands and declare credential handles rather than ambient secret reads.
They include package pin fields as `pending` so real bundle identifiers can be
added without changing the contract.

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
- explicit full Node/V8/libuv blocker declaration.
