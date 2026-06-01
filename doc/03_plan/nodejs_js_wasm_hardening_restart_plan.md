# NodeJS JS/WASM Hardening Restart Plan

Last updated: 2026-06-01

## Active Goal

`$sp_dev nodejs level js engine and web browser js, wasm hardening`

Harden the Simple JavaScript runtime, Node-compatible API surface, browser
JavaScript, fetch-driven WebAssembly loading, and WebGPU-adjacent WASM behavior
so capability boundaries are explicit, denial paths are verified, and positive
runtime paths are covered by executable tests.

This goal is not complete. Do not mark the active goal complete until the
remaining OS-boundary hardening, Phase 6 QEMU validation, and documented
WebGPU/WASM scope decisions are all either implemented or explicitly split into
follow-up goals.

## Crash Restart Summary

GitHub `origin/main` observed during this checkpoint:

- `e90554060d test: populate ai cli fat32 image host-side`

Latest pushed JS/WASM hardening commit at turn start:

- `e90554060d test: populate ai cli fat32 image host-side`

Use clean worktrees from `origin/main` for pushable JS/WASM slices. The main
workspace may contain unrelated GUI/perf/local changes. Do not revert unrelated
dirty files and do not commit them into this goal.

Current in-flight worktree:

- Path: `/tmp/simple-js-wasm-qemu-audit`
- Base: clean worktree from `origin/main`; rebase before pushing if remote moved.
- Slice: Phase 5 VFS-manager file-grant enforcement.
- Status: Phase 5 process-grant syscall enforcement implemented and focused
  verification in progress.
- Evidence from pushed runtime grant slices: `node_api_conformance_spec.spl`
  passed 149 scenarios, `simpleos_ai_cli_js_node_port_spec.spl` passed 25
  scenarios, and `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.

If this session crashes, restart by fetching `origin/main`, creating a clean
worktree, reading this file, then continuing at the first unchecked item in
`Remaining Goal Plan`.

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
- `29d326438a feat: enforce node process grants`
- `ba84554e3a docs: reconcile js wasm hardening status`
- `c4966a310a test: add ai cli qemu lane harness`
- `ecbc0c9db8 test: stage ai cli qemu smoke package`
- `68e80d281b test: prove ai cli fat32 staging ingestion`

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
- Status docs now explicitly distinguish runtime grant conformance from
  still-pending OS VFS, socket, and process boundary enforcement.
- Phase 6 now has a contract-first QEMU lane harness, host-side smoke package
  staging, a disk-import manifest, and a host FAT32 tree-populator test proving
  staged AI CLI payload bytes can be mirrored into a formatted image.
- VFS-manager file-grant enforcement now carries an optional `AiCliManifest`
  policy and denies ungranted paths before VFS path routing. Unit coverage
  proves allowed workspace access, sibling-prefix denial, invalid relative path
  denial, denied rename targets, and clearing the manifest.
- Process syscall enforcement now gates exec, spawn_binary, and direct spawn
  paths through `process_grants` before executable resolution. Unit coverage
  proves allowed `/usr/bin/git`, denied `/bin/sh`, denied legacy sentinel spawn,
  and denied exec image replacement.
- POSIX socket enforcement now gates connect, bind, and listen paths through
  `network_grants` before netstack IPC. Unit coverage proves ungranted connect,
  bind, and listen endpoints return `-EACCES`.

## Remaining Goal Plan

1. Phase 5 OS-boundary hardening.
   - Keep the Node-compatible runtime grant work marked complete.
   - VFS-manager `file_grants` enforcement is implemented and covered by
     `test/unit/os/services/vfs/vfs_spec.spl`; do not broaden this claim to
     socket/process boundaries.
   - Socket-layer `network_grants` enforcement is implemented and covered by
     `test/unit/os/posix/socket_compat_spec.spl`; do not broaden this claim to
     QEMU guest network evidence.
   - Spawn/exec-layer `process_grants` enforcement is implemented and covered
     by `test/unit/os/kernel/ipc/syscall_spec.spl`; do not broaden this claim
     to socket boundaries.
   - Do not check the OS-layer boxes in
     `doc/03_plan/simpleos_nodejs_ai_cli_migration.md` until tests or QEMU
     evidence reach those exact layers.

2. Phase 6 QEMU runtime provisioning.
   - `scripts/check-ai-cli-qemu-lanes.shs --contract-only` now derives required
     marker files from `src/os/ai_cli_js_node_contract.spl` and records the
     selected app/target lane contract without claiming guest evidence.
   - `scripts/check-ai-cli-qemu-lanes.shs --stage-smoke-package` now writes the
     selected host-side smoke package files into the FAT32-like staging tree and
     exits with `stage-smoke-package`, not `pass`, because no guest serial
     evidence has been observed.
   - Stage mode also writes `build/ai-cli-qemu-lanes/reports/ai-cli-disk-import.tsv`
     with guest paths, host paths, byte counts, and digests for the next
     disk-image ingestion slice.
   - `test/unit/os/port/host_fat32_tree_populator_spec.spl` now proves the
     existing FAT32 host-tree populator can ingest the AI CLI staging path shape
     (`sys/runtime/node-compatible/x86/runtime.smf` plus `sys/apps/codex/*`)
     into a formatted image. This is still host-side readiness, not guest boot
     evidence.
   - Current in-progress slice adds
     `scripts/check-ai-cli-qemu-lanes.shs --stage-smoke-package
     --populate-fat32-image <img>` so the harness can materialize the selected
     smoke package and mirror it into an existing formatted FAT32 image. The
     expected success marker is `fat32_populate_status=host-image-populated`.
     This remains host-side image evidence, not guest/QEMU serial evidence.
   - The FAT32 driver must resolve its own 8.3 aliases for long names such as
     `node-compatible`; otherwise the host populator can create the directory,
     reload the image, and fail to traverse the original long path.
   - Audit `ai_cli_qemu_lane`, staged package generation, launcher marker
     output, and runtime artifact assumptions.
   - Provision a Node-compatible runtime artifact and CLI bundles into the
     guest-visible FAT32 image path.
   - Boot x86_64, RISC-V, and AArch64 lanes.
   - Capture real guest serial markers for runtime start, CLI smoke, hardening
     denials, and `[ai-cli] hardening:ok app=<tool>`.
   - Update `ai_cli_qemu_lane` from `blocked-runtime-artifact` to `ready` only
     after real guest evidence exists.

3. WebGPU/WASM scope closure.
   - Current browser-side asset loading, `WebAssembly.instantiate`, nested
     Promise assimilation, software WebGPU metadata, and the minimal declared
     `webgpu.requestAdapter` host import are covered.
   - Full WASM-originated WebGPU ABI, hardware/driver-backed WebGPU execution,
     WebGPU CTS conformance, and pixel-stable hardware rendering are split from
     this goal as follow-up scope. This goal keeps the current software-backed
     metadata/API coverage and minimal declared host import callback.
   - `doc/03_plan/sys_test/webgpu_js_wasm_simple.md` now reconciles
     REQ-WGPU-001 through REQ-WGPU-005 with the current system-spec coverage
     instead of listing stale "add system spec example" gaps.
   - Capture release-grade evidence for
     `test/system/app/browser/feature/webgpu_js_wasm_simple_spec.spl`; the
     focused fetch/WASM and browser host specs pass, but the full system spec
     may need a longer runner window or split evidence.

4. Focused verification before any final completion claim.
   - Run the Node conformance spec.
   - Run the SimpleOS AI CLI manifest/spec contract.
   - Run the browser WebGPU JS/WASM system spec.
   - Run `find doc/06_spec -name '*_spec.spl' | wc -l` and require `0`.
   - Run `git diff --check`.

5. Release readiness.
   - Only after the above is complete or explicitly split, run `$verify`.
   - Do not run `$release` until verify reports `STATUS: PASS`.

## Current Next Slice

This turn's active slice is Phase 5 VFS-manager `file_grants` enforcement. The
slice is complete only after these checks pass and the commit is pushed:

- `SIMPLE_LIB=<worktree>/src /home/ormastes/dev/pub/simple/bin/simple check src/os/services/vfs/vfs.spl test/unit/os/services/vfs/vfs_spec.spl`
- `SIMPLE_LIB=<worktree>/src /home/ormastes/dev/pub/simple/bin/simple test test/unit/os/services/vfs/vfs_spec.spl --mode=interpreter --clean`
- `SIMPLE_LIB=<worktree>/src /home/ormastes/dev/pub/simple/bin/simple test test/system/os/simpleos_ai_cli_js_node_port_spec.spl --mode=interpreter --clean`
- `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0`
- `git diff --check`

Recommended next implementation slice after this commit: Phase 6 guest-visible
runtime provisioning and real QEMU serial evidence. Keep host-side FAT32
package/image readiness separate from guest validation.

Phase 6 provisioning commands remain useful for the separate QEMU runtime slice.
Do not mark Phase 6 complete from host-side package generation or image
population alone. It needs guest serial evidence.

Initial harness command:

```sh
SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple SIMPLE_LIB=<worktree>/src \
  sh scripts/check-ai-cli-qemu-lanes.shs --contract-only
```

Host-side staging command:

```sh
SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple SIMPLE_LIB=<worktree>/src \
  sh scripts/check-ai-cli-qemu-lanes.shs --stage-smoke-package --target x86 --app codex
```

The staging command should report `ai_cli_qemu_lanes_status=stage-smoke-package`
and an `import_manifest=.../ai-cli-disk-import.tsv` line. Treat that manifest as
input to the FAT32 image population work, not as QEMU evidence.

Host-side FAT32 image population command:

```sh
SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple SIMPLE_LIB=<worktree>/src \
  sh scripts/check-ai-cli-qemu-lanes.shs --stage-smoke-package \
  --populate-fat32-image <formatted-fat32.img> --target x86 --app codex
```

The image-population command should report
`fat32_populate_status=host-image-populated` and
`ai_cli_qemu_lanes_status=stage-smoke-package`. It proves host image ingestion
only; do not check off full QEMU validation until a booted guest emits the
required serial markers.

Promotion commands after runtime provisioning exists:

```sh
sh scripts/check-ai-cli-qemu-lanes.shs --target x86 --app all
sh scripts/check-ai-cli-qemu-lanes.shs --target riscv --app all
sh scripts/check-ai-cli-qemu-lanes.shs --target arm --app all
```

## Immediate Next Commands

Use the active runner from the main workspace when testing a clean worktree:

```sh
SIMPLE_LIB=<worktree>/src /home/ormastes/dev/pub/simple/bin/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --clean
SIMPLE_LIB=<worktree>/src /home/ormastes/dev/pub/simple/bin/simple test test/system/os/simpleos_ai_cli_js_node_port_spec.spl --mode=interpreter --clean
SIMPLE_LIB=<worktree>/src /home/ormastes/dev/pub/simple/bin/simple test test/system/app/browser/feature/webgpu_js_wasm_simple_spec.spl --mode=interpreter --clean
```

Known current caveat:

- The focused Node-compatible runtime grant conformance passes, but this does
  not prove OS VFS-layer, socket-layer, or kernel process-spawn enforcement.
  Keep those Phase 5 checklist items open unless a later slice verifies the
  actual OS boundary.

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
