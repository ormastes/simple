<!-- codex-design-draft -->
# SimpleOS AI CLI JS/Node Port Contract Draft

Status: pre-requirements draft. Do not treat this as final design until
`doc/02_requirements/feature/simpleos_ai_cli_js_node_port.md` and
`doc/02_requirements/nfr/simpleos_ai_cli_js_node_port.md` exist.

## Purpose

Map the Codex, Claude, and Gemini CLI port goal to concrete SimpleOS runtime
surfaces before choosing the final implementation path.

## Runtime Contract Matrix

| Node/CLI need | SimpleOS surface | Current status | Next seam |
|---|---|---|---|
| CLI process launch | `src/os/apps/shell/exec.spl`, `src/os/kernel/loader/fs_exec_spawn.spl` | Existing filesystem exec path | Add AI CLI manifest entries and smoke markers after requirements are selected |
| Capability-gated exec | `src/os/kernel/loader/cap_exec_gate.spl`, `src/os/kernel/types/capability_types.spl` | FileExec + ProcessSpawn gate exists | Extend manifest-to-capability mapping for file/process/network/credential grants |
| Terminal/stdio | `src/os/apps/terminal/terminal.spl`, `src/os/apps/shell/**` | Shell and terminal apps exist | Define raw-mode, prompts, stdout/stderr, and exit status behavior required by AI CLIs |
| Filesystem | `src/os/services/vfs/**`, `src/os/services/fat32/**` | FAT/VFS app reads and fs-exec lanes exist | Define allowed workspace, config, cache, package, and temp paths |
| Process APIs | `src/os/kernel/process_compat.spl`, `src/os/posix/process_compat.spl`, `src/os/sosix/process_compat.spl` | Process compatibility files exist | Decide whether Node `child_process` maps to SimpleOS spawn or is denied by default |
| Network | `src/os/drivers/virtio/network_device.spl`, `src/os/apps/network_monitor/network_monitor.spl` | Virtio network smoke markers exist | Add manifest-declared API endpoint/port grants |
| TLS/HTTPS | `src/os/kernel/net/tls_shim.spl`, `src/os/tls12/**`, `src/os/tls13/**` | TLS components exist | Define minimum HTTPS client contract for AI API calls |
| Timers/event loop | `src/os/async/os_executor.spl` | Async executor exists | Map Node timers/promises to bounded SimpleOS timers |
| JavaScript execution | `src/lib/gc_async_mut/gpu/browser_engine/browser_script_execute.spl` | Browser-oriented script support only | Decide between contract-first shim, real Node/V8, or bundled runtime |
| npm/module loading | none dedicated | Missing | Prefer offline pinned package manifests for QEMU validation |
| Credentials | capability system only | No AI credential store identified | Require explicit secret mount/env grant; ambient reads denied |
| Multi-arch QEMU | `src/os/_QemuRunner/scenario_disks.spl`, `src/os/_QemuRunner/scenario_exec.spl` | RISC-V/x86/ARM fs-exec lanes exist | Add JS runtime + AI CLI serial marker contract per architecture |

## CLI Manifest Shape

The eventual manifest should describe each AI CLI without granting ambient OS
authority:

```text
app_id: codex | claude | gemini
runtime: node-compatible | bundled-node | simple-js-agent
entry: /sys/apps/<app>/...
args: [...]
needs_terminal: true
file_grants: [workspace, config, cache, temp]
process_grants: [spawn-denied-by-default or declared tools]
network_grants: [api host/port families]
credential_grants: [named secret handles]
qemu_markers: [launch, denied-host-escape, denied-ambient-secret, bounded-network]
```

## Hardening Rules

- File access is denied unless the path is covered by a manifest grant.
- Process spawning is denied unless the manifest declares the child command or
  the scenario is an explicit negative test.
- Network access is denied unless the manifest declares the endpoint class.
- Credential access is denied unless the manifest declares a named secret
  handle.
- Host shell escapes are not accepted as a substitute for guest-side execution
  evidence.

## First Implementation Candidate

After final requirement selection, the smallest code step is a pure manifest
adapter that converts an AI CLI manifest into SimpleOS capability requirements
and QEMU marker expectations. That can be tested without a full Node port, then
used to drive the real runtime lane.

## Open Requirement Decisions

- Feature path: contract-first, bundled Node first, minimal JS agent, or
  SEA/bundle-oriented port.
- NFR gate: security-first, portability-first, or reproducibility-first.
- Target spelling: the request says `x85`; current draft interprets it as x86.
