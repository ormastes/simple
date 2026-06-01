# NodeJS JS/WASM Hardening Restart Plan

Last updated: 2026-06-01

## Active Goal

`$sp_dev nodejs level js engine and web browser js, wasm hardening`

Harden the Simple JavaScript runtime, Node-compatible API surface, browser
JavaScript, fetch-driven WebAssembly loading, and WebGPU-adjacent WASM behavior
so capability boundaries are explicit, denial paths are verified, and positive
runtime paths are covered by executable tests.

This goal is not complete. Do not mark the active goal complete until Phase 5
runtime boundaries, Phase 6 QEMU validation, and the documented WebGPU/WASM
scope decisions are all either implemented or explicitly split into follow-up
goals.

## Crash Restart Summary

GitHub `origin/main` is currently:

- `034942e82a feat: enforce node network grants`

Use clean worktrees from `origin/main` for pushable JS/WASM slices. The main
workspace may contain unrelated GUI/perf/local changes. Do not revert unrelated
dirty files and do not commit them into this goal.

Current in-flight worktree:

- Path: `/tmp/simple-js-wasm-process-grants`
- Base: `origin/main` at `034942e82a`
- Slice: Node-compatible runtime process grants for `child_process.spawn`.
- Status: focused conformance passes locally; push the current
  `feat: enforce node process grants` commit if it is not already on GitHub.
- Evidence: `node_api_conformance_spec.spl` passes 149 scenarios,
  `simpleos_ai_cli_js_node_port_spec.spl` passes 25 scenarios, and
  `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0`.

## Authoritative Files

- `.spipe/nodejs-js-wasm-hardening/state.md`
- `doc/03_plan/simpleos_nodejs_ai_cli_migration.md`
- `doc/03_plan/sys_test/simpleos_ai_cli_js_node_port.md`
- `doc/03_plan/sys_test/webgpu_js_wasm_simple.md`
- `doc/03_plan/nodejs_js_wasm_hardening_restart_plan.md`
- `test/system/os/simpleos_ai_cli_js_node_port_spec.spl`
- `test/system/app/browser/feature/webgpu_js_wasm_simple_spec.spl`
- `test/feature/js/node_api_conformance_spec.spl`

## Pushed Progress

Pushed JS/WASM hardening commits include:

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
- `64ababc735f5 docs: mark credential env slice pushed`
- `18f866f497 feat: enforce node file grants`
- `034942e82a feat: enforce node network grants`
- `feat: enforce node process grants` is the current process-grant slice being synced

Completed evidence:

- Browser `fetch` -> `arrayBuffer` -> `WebAssembly.instantiate` promise chain is
  covered, including nested host Promise assimilation from WebGPU callbacks.
- BrowserSession exposes deterministic WebGPU metadata and the software adapter
  through the same WASM-fetch session.
- Minimal declared WASM host import `webgpu.requestAdapter` is covered and
  unsafe direct imports remain denied.
- Node-compatible conformance covers deterministic API subsets and fail-closed
  file, network, process, credential, crypto entropy, and terminal denials.
- Manifest contract emits Node-style `--experimental-permission` flags.
- Deno comparison flags and hardening serial marker fragments are documented.
- Credential env grants are wired into actual JS runtime `process.env` and
  `require("process").env`; ambient env reads remain undefined.
- Node-compatible `fs` grant conformance now covers allowed read/write status,
  read data for a granted file, sibling-prefix denial, and relative-path denial.
- Node-compatible network grant conformance now covers allowed and denied
  `net.createConnection`, `http.request`, `https.request`, and
  `http.Server.listen` endpoints.
- Node-compatible process grant conformance now covers allowed `node` spawn,
  mismatched command denial, and shell-style command string rejection.

## Remaining Goal Plan

1. Push runtime process grants if needed.
   - The current `feat: enforce node process grants` commit is locally verified.
   - If GitHub already contains it, start the focused Phase 5/6 reconciliation
     and QEMU/runtime provisioning audit next.

2. Reconcile Phase 5 OS/VFS wording.
   - Only check `File access: enforce file_grants at VFS layer` in
     `simpleos_nodejs_ai_cli_migration.md` if evidence reaches the OS VFS
     boundary.
   - If current work only covers Node-compatible runtime `fs`, record that as
     runtime complete and leave OS VFS enforcement pending.

3. Run full focused verification.
   - Node conformance spec.
   - SimpleOS AI CLI manifest/spec contract.
   - Browser WebGPU JS/WASM system spec.
   - `find doc/06_spec -name '*_spec.spl' | wc -l` must print `0`.

4. Phase 6 QEMU validation.
   - Provision Node-compatible runtime artifact and CLI bundles.
   - Boot x86_64, RISC-V, and AArch64 lanes.
   - Capture serial markers for runtime, CLI smoke, and hardening OK.
   - Update `ai_cli_qemu_lane` from `blocked-runtime-artifact` only after real
     guest evidence exists.

5. WebGPU/WASM final scope decision.
   - Current browser-side asset loading, instantiation, nested Promise
     assimilation, and minimal declared host import callback are covered.
   - Full WASM-originated WebGPU ABI and hardware/driver-backed WebGPU execution
     remain incomplete unless intentionally split into a later goal.

## Immediate Next Commands

Use the active runner from the main workspace when testing the clean worktree:

```sh
cd /tmp/simple-js-wasm-file-grants
SIMPLE_LIB=/tmp/simple-js-wasm-file-grants/src /home/ormastes/dev/pub/simple/bin/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/runtime.spl test/feature/js/node_api_conformance_spec.spl
SIMPLE_LIB=/tmp/simple-js-wasm-file-grants/src /home/ormastes/dev/pub/simple/bin/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --clean
```

Known current caveat:

- The focused Node-compatible `fs` runtime conformance passes, but this does
  not prove OS VFS-layer enforcement. Keep the Phase 5 VFS checklist item open
  unless a later slice verifies the actual VFS boundary.

## Verification Checklist Per Slice

Run the narrowest relevant checks first, then expand:

```sh
SIMPLE_LIB=src bin/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src bin/simple test test/system/os/simpleos_ai_cli_js_node_port_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src bin/simple test test/system/app/browser/feature/webgpu_js_wasm_simple_spec.spl --mode=interpreter --clean
find doc/06_spec -name '*_spec.spl' | wc -l
git diff --check
git status --short
```

Expected layout result:

- `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0`.

## Sync Rule

After each small completed slice, commit and push only that slice.

Preferred clean-worktree Git flow:

```sh
git fetch origin
git rebase origin/main
git status --short
git add <explicit files>
git commit -m "<message>"
env -u GITHUB_TOKEN git push origin HEAD:main
git ls-remote origin refs/heads/main
```

If push is rejected, fetch/rebase, resolve only files owned by the slice, rerun
the focused checks, and push again.
