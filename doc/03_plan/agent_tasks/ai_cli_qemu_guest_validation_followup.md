# AI CLI QEMU Guest Validation Follow-Up

Last updated: 2026-06-01

## Goal

Produce real SimpleOS guest serial evidence for the AI CLI JS/Node hardening
lanes after a guest-executable Node-compatible runtime artifact and launcher
handoff exist.

## Why This Is Split

The current hardening goal has implemented and verified the contract, host-side
package staging, FAT32 image population, JS runtime grants, OS VFS/process/socket
grant gates, and WebGPU/WASM browser scope. The remaining Phase 6 work requires
guest execution of a runtime artifact, not just host package generation.

Fresh evidence from 2026-06-01:

- `scripts/check-ai-cli-qemu-lanes.shs --contract-only` passes for 9 lanes and
  reports `ai_cli_qemu_lanes_status=contract-only`.
- `scripts/check-ai-cli-qemu-lanes.shs --stage-smoke-package --target x86 --app codex`
  materializes the host package and reports
  `ai_cli_qemu_lanes_status=stage-smoke-package`.
- Default validation for `--target x86 --app codex` fails because
  `build/os/ai-cli-x86_64.serial.log` is missing.

## Required Work

1. Build or package a guest-executable Node-compatible runtime artifact for each
   selected target under `/sys/runtime/node-compatible/<target>/runtime.smf`.
2. Add a legitimate SimpleOS launcher handoff that runs
   `/sys/apps/<app>/launch.spl` or an equivalent compiled launcher inside the
   guest.
3. Ensure the launched runtime reads `/sys/apps/<app>/AI_MANIFEST.SDN`, applies
   file/process/network/credential grants, runs the bundled `<app>.js` smoke
   entry, exercises denial paths, and emits the required `[ai-cli] ...` markers.
4. Boot x86_64, RISC-V, and AArch64 lanes and capture serial logs at
   `build/os/ai-cli-x86_64.serial.log`,
   `build/os/ai-cli-riscv64.serial.log`, and
   `build/os/ai-cli-arm64.serial.log`.
5. Pass `scripts/check-ai-cli-qemu-lanes.shs --target all --app all` without
   `--contract-only` or `--stage-smoke-package`.

## Non-Acceptance

Host-side generated files, FAT32 image population, staged marker payloads, and
synthetic serial logs are not guest validation evidence.
