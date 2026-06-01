# NodeJS JS/WASM Hardening Restart Plan

## Goal

Active SPipe goal:

`$sp_dev nodejs level js engine and web browser js, wasm hardening`

Harden the Simple JavaScript runtime so NodeJS-compatible APIs, browser JavaScript, fetch-driven WebAssembly loading, and WebGPU-adjacent WASM execution have explicit capability boundaries and verified positive and denial behavior.

## Current Remote Head

As of 2026-06-01, GitHub `origin/main` is:

- `24182092ea11 feat: enforce node credential env grants`

Do not assume the dirty worktree belongs to this goal. There are unrelated GUI/vector/image/perf evidence changes in the working copy. Commit only explicit JS/WASM hardening files for this goal.

## Authoritative State Files

- `.spipe/nodejs-js-wasm-hardening/state.md`
- `doc/03_plan/simpleos_nodejs_ai_cli_migration.md`
- `doc/03_plan/sys_test/webgpu_js_wasm_simple.md`
- `doc/03_plan/sys_test/simpleos_ai_cli_js_node_port.md`
- `test/system/os/simpleos_ai_cli_js_node_port_spec.spl`
- `test/system/app/browser/feature/webgpu_js_wasm_simple_spec.spl`
- `test/feature/js/node_api_conformance_spec.spl`

## Completed And Pushed Slices

Pushed commits for this goal:

- `c6d4387b900d test: harden js wasm browser promise chain`
- `9b59072c1535 test: harden ai cli node capability denials`
- `74c53b12fb0 test: add ai cli permission flags`
- `d4c913ceffb0 test: record node hardening conformance`
- `333a1d39f84a test: harden js wasm browser bridge`
- `ac2c5bac3d72 test: record ai cli deno hardening markers`
- `785cbbac2149 docs: add js wasm hardening restart plan`
- `33049d36d746 test: tighten ai cli file grant boundary`
- `02aadfe913eb test: tighten ai cli network grant boundary`
- `778af6370bb2 test: tighten ai cli process grant boundary`
- `8433c511c560 test: tighten ai cli credential grant boundary`
- `2a400b9eb510 test: harden webgpu wasm promise assimilation`
- `24182092ea11 feat: enforce node credential env grants`

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

6. Boundary decision helpers.
   - File grant helpers now reject sibling-prefix escapes like `/home/user/workspace` when only `/home/user/work` is granted.
   - Network grant helpers normalize and deny malformed or undeclared socket endpoints.
   - Process grant helpers normalize path-qualified commands and deny shell-style command strings.
   - Credential decision helpers deny ambient env and inline API-key token shapes.

7. WebGPU nested Promise assimilation.
   - BrowserSession WASM fetch chains now assimilate nested host promises returned by WebGPU callbacks.
   - `webgpu_js_wasm_simple_spec.spl` covers the `fetch` -> `arrayBuffer` -> `WebAssembly.instantiate` -> `Promise.resolve(navigator.gpu.requestAdapter())` path.

8. Node-compatible credential/env runtime grants.
   - `JsRuntime.grant_node_credential(handle, value)` maps handles such as `openai-api-key` to env keys such as `OPENAI_API_KEY`.
   - `process.env.OPENAI_API_KEY` and `require('process').env.OPENAI_API_KEY` return only explicitly granted values.
   - Ambient values such as `process.env.PATH` and undeclared provider keys remain `undefined`.
   - The Phase 5 credential checklist is checked in `doc/03_plan/simpleos_nodejs_ai_cli_migration.md`.

Last recorded verification for the credential/env runtime slice:

```sh
SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/js/engine/interpreter.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/runtime.spl test/feature/js/node_api_conformance_spec.spl
SIMPLE_LIB=src bin/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src bin/simple test test/system/os/simpleos_ai_cli_js_node_port_spec.spl --mode=interpreter --clean
find doc/06_spec -name '*_spec.spl' | wc -l
```

Expected current local evidence:

- `node_api_conformance_spec.spl`: 143 scenarios passing.
- `simpleos_ai_cli_js_node_port_spec.spl`: 25 scenarios passing.
- `doc/06_spec` stray `.spl` count: `0`.

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

- `simpleos_ai_cli_js_node_port_spec.spl`: 25 scenarios passing on the current local slice.
- `webgpu_js_wasm_simple_spec.spl`: 106 scenarios passing at the pushed WebGPU promise-assimilation baseline.
- `node_api_conformance_spec.spl`: 143 scenarios passing on the current local credential/env slice.
- `doc/06_spec` stray `.spl` count: `0`.

## Remaining Work

Phase 5 unchecked hardening items in `doc/03_plan/simpleos_nodejs_ai_cli_migration.md`:

- File access: enforce `file_grants` at the VFS boundary and deny undeclared paths.
- Network: enforce `network_grants` at the socket boundary and allowlist endpoints only.
- Process: enforce `process_grants` and deny undeclared spawns.

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

4. Re-run Node conformance and OS contract specs.
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
