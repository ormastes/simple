# NodeJS JS/WASM Hardening Restart Plan

## Goal

Active SPipe goal:

`$sp_dev nodejs level js engine and web browser js, wasm hardening`

Harden the Simple JavaScript runtime so NodeJS-compatible APIs, browser JavaScript, fetch-driven WebAssembly loading, and WebGPU-adjacent WASM execution have explicit capability boundaries and verified positive and denial behavior.

## Current Remote Head

As of 2026-06-01, `origin/main` is:

- `ac2c5bac3d72 test: record ai cli deno hardening markers`

Do not assume the dirty worktree belongs to this goal. There are unrelated GUI/vector/image evidence changes in the working copy. Commit only explicit JS/WASM hardening files for this goal.

## Authoritative State Files

- `.spipe/nodejs-js-wasm-hardening/state.md`
- `doc/03_plan/simpleos_nodejs_ai_cli_migration.md`
- `doc/03_plan/sys_test/webgpu_js_wasm_simple.md`
- `doc/03_plan/sys_test/simpleos_ai_cli_js_node_port.md`
- `test/system/os/simpleos_ai_cli_js_node_port_spec.spl`
- `test/system/app/browser/feature/webgpu_js_wasm_simple_spec.spl`
- `test/feature/js/node_api_conformance_spec.spl`

## Completed And Pushed Slices

1. Browser WASM promise chain and WebAssembly hardening.
   - Fixed BrowserSession `fetch` -> `arrayBuffer` -> `WebAssembly.instantiate`.
   - Hardened Promise metadata/state handling and promise-safe callback invocation.
   - Mirrored host Promise and `Response.arrayBuffer` behavior across runtime families.

2. Node-compatible denial coverage.
   - Strengthened hardening detection for file, network, process, and credential/environment escape signatures.
   - Executable Node API conformance covers deterministic positive APIs and fail-closed denials.

3. Permission flags.
   - `AiCliManifest` now emits Node-style `--experimental-permission` flags for file, child process, network, and credential/env grants.
   - Deny-all manifests emit only the base permission flag.

4. Browser JS/WASM/WebGPU bridge.
   - System spec proves `fetch` -> `arrayBuffer` -> `WebAssembly.instantiate` reaches WebGPU global metadata.
   - Same BrowserSession resolves deterministic `navigator.gpu.requestAdapter()` software-adapter metadata.
   - WASM can invoke a bounded declared host import `webgpu.requestAdapter`.
   - `simple_browser_wasm_gui_contract()` allows only the narrow `webgpu.requestAdapter` bridge token and denies direct device/queue/global imports.

5. Deno comparison and hardening OK markers.
   - `AiCliManifest` now emits Deno-style comparison flags: `--allow-read`, `--allow-write`, `--allow-net`, `--allow-run`, `--allow-env`.
   - QEMU marker fragments and staged launchers explicitly include `[ai-cli] hardening:ok app=<tool>`.

## Last Known Passing Commands

Run these first after a crash to confirm the pushed baseline:

```sh
SIMPLE_LIB=src bin/simple check src/os/ai_cli_js_node_contract.spl
SIMPLE_LIB=src bin/simple test test/system/os/simpleos_ai_cli_js_node_port_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src bin/simple test test/system/app/browser/feature/webgpu_js_wasm_simple_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src bin/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --clean
find doc/06_spec -name '*_spec.spl' | wc -l
```

Expected evidence from the latest slices:

- `simpleos_ai_cli_js_node_port_spec.spl`: 21 scenarios passing.
- `webgpu_js_wasm_simple_spec.spl`: 105 scenarios passing.
- `node_api_conformance_spec.spl`: 142 scenarios passing.
- `doc/06_spec` stray `.spl` count: `0`.

## Remaining Work

Phase 5 unchecked hardening items in `doc/03_plan/simpleos_nodejs_ai_cli_migration.md`:

- File access: enforce `file_grants` at the VFS boundary and deny undeclared paths.
- Network: enforce `network_grants` at the socket boundary and allowlist endpoints only.
- Process: enforce `process_grants` and deny undeclared spawns.
- Credentials: enforce `credential_grants` and block ambient env var reads.

Phase 6 remains unchecked:

- Full QEMU validation for x86_64, RISC-V, and AArch64.
- FAT32 disk image provisioning with runtime + CLI bundles.
- Automated serial capture and marker verification.
- Update `ai_cli_qemu_lane` runtime status from `blocked-runtime-artifact` to `ready` only when the runtime artifact exists and the QEMU smoke passes.

WebGPU/WASM remaining gap:

- Nested returned-Promise assimilation for WebGPU callbacks is now covered by `webgpu_js_wasm_simple_spec.spl`.
- Complete WASM-originated WebGPU ABI and real hardware/driver WebGPU execution are not implemented.

## Recommended Next Slice

Implement one enforcement boundary at a time and sync after each passing slice.

1. File grant boundary.
   - Add a small contract/API that models VFS open/read/write decisions from `AiCliManifest.file_grants`.
   - Cover exact allowed prefixes, prefix escape cases, empty grants, and deny reason strings.
   - Update `simpleos_ai_cli_js_node_port_spec.spl`, generated `doc/06_spec`, `.spipe` state, and the Phase 5 checklist only if the evidence truly proves the VFS boundary claim.

2. Network grant boundary.
   - Add socket endpoint decision helpers for host:port allowlists.
   - Cover undeclared endpoints, wildcard behavior if supported, and malformed endpoint denial.

3. Process grant boundary.
   - Add process spawn decision helpers for command allowlists.
   - Cover path-qualified commands, shell escape denial, and undeclared spawn denial.

4. Credential grant boundary.
   - Add credential/env read decision helpers.
   - Cover allowed handles, ambient `process.env`/`Deno.env` denial, and API key token signature denial.

5. Re-run Node conformance and OS contract specs.
   - Regenerate SPipe manuals after every spec change.
   - Keep `find doc/06_spec -name '*_spec.spl' | wc -l` at `0`.

## Sync Rule

After each small completed slice:

```sh
jj commit <explicit files> -m "<message>"
jj git fetch
jj rebase -d main@origin
jj bookmark set main -r @-
env -u GITHUB_TOKEN jj git push --bookmark main
git ls-remote origin refs/heads/main
```

If unrelated commits appear between `main@origin` and `@-`, do not use `@-` blindly. Move `main` only to the intended JS/WASM hardening commit.
