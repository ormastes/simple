<!-- codex-design -->
# Architecture: SimpleOS AI CLI JS/Node Port

## Scope

This architecture covers the selected contract-first slice for hardened
JavaScript/Node-compatible AI CLI execution. It does not claim full Node.js,
V8, libuv, npm, or authenticated Codex/Claude/Gemini execution in QEMU.

## Pattern

Use a data-first runtime contract module that sits between packaged AI CLI app
descriptions and existing SimpleOS capability/QEMU lanes:

- `AiCliManifest` declares identity, runtime, entrypoint, package pin fields,
  file/process/network/credential/terminal grants, and QEMU marker fragments.
- Built-in constructors define deterministic Codex, Claude, and Gemini smoke
  manifests without live credentials.
- Staged smoke package constructors now use concrete package/runtime identifiers
  for the contract artifact:
  `0.1.0-smoke.20260530`,
  `manifest-package-smoke:<app>:20260530`, and
  `simple-js-agent-smoke-stub@20260530`.
- Summary and denial helpers provide a stable compatibility contract that later
  provisioning code can consume before a real Node runtime is bundled.

This is an MDSOC virtual capsule: AI CLI runtime policy crosses app packaging,
capability checks, network/credential boundaries, and QEMU evidence, but the
first slice keeps those concerns in a narrow contract module rather than
weaving ad hoc checks into launchers.

## Runtime Boundaries

The module owns:

- manifest validation and supported runtime names;
- fail-closed file, process, network, credential, and terminal grant checks;
- deterministic capability summaries;
- QEMU marker data for `riscv`, `x86`, `x85` as x86, and `arm`;
- a Bun-informed Simple JS runtime profile that captures a cohesive
  runtime/package/transpile/bundle/test surface without adopting Bun's
  Zig/JavaScriptCore internals;
- a generated-WASM/browser GUI contract with allowed imports, denied host
  escapes, required exports, and browser/QEMU evidence markers;
- blocker text for the later full Node/V8/libuv implementation layer.
- guest serial fragments for runtime start, CLI smoke start, hardening denial,
  and blocker reporting with
  `blocked:no-full-node-v8-libuv-artifact-20260530`.

The module does not own:

- actual JavaScript parsing or execution;
- Node.js ABI/libuv/V8 porting;
- JavaScriptCore or Zig runtime embedding;
- npm package installation;
- live API authentication;
- host shell fallback success markers.

## Hot Paths And Caches

Manifest validation and grant checks are in-memory linear scans over small
manifest arrays. They must not shell out, scan the tree, read package files per
request, or sleep. Future package provisioning may cache parsed manifests by
package id/version/checksum, with invalidation on package artifact changes.

## Performance Targets

- Warm manifest validation: under 1 ms per manifest on host tests.
- Representative grant check: under 1 ms and no allocation beyond caller data.
- RSS impact: no persistent runtime allocation beyond the manifest arrays in
  this slice.

## Evidence Strategy

Focused SPipe tests prove REQ-001..REQ-006, REQ-008..REQ-012, and NFR-001..NFR-007
through pure contract behavior. REQ-007 and AC-7 are proven by explicit blocker
fields and docs until QEMU runtime provisioning exists.
