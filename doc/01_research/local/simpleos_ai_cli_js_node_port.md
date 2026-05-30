<!-- codex-research -->
# Local Research: SimpleOS AI CLI JS/Node Port

## Request

Harden JavaScript, port Node.js, and run Codex, Claude, and Gemini CLI on
SimpleOS under QEMU for RISC-V, x86, and ARM.

## Existing Assets

- SPipe state: `.spipe/simpleos-ai-cli-js-node-port/state.md`.
- Browser/script surface:
  `src/lib/gc_async_mut/gpu/browser_engine/browser_script_execute.spl`,
  `browser_script_render.spl`, and `simple_web_script_renderer.spl` exist, but
  the browser engine is HTML/rendering oriented and is not a Node-compatible
  runtime.
- Terminal/shell surface:
  `src/os/apps/terminal/terminal.spl` and `src/os/apps/shell/**` provide
  interactive command surfaces. `src/os/apps/shell/exec.spl` routes commands
  into filesystem-backed exec.
- Process/exec surface:
  `src/os/kernel/loader/fs_exec_spawn.spl`,
  `x86_64_fs_exec_spawn.spl`, `arm64_fs_exec_spawn.spl`, and
  `cap_exec_gate.spl` already model executable loading and capability-gated
  spawning.
- Capability/security surface:
  `src/os/kernel/ipc/capability.spl`,
  `src/os/kernel/types/capability_types.spl`,
  `src/os/kernel/scheduler/capability_bridge.spl`, and
  `src/os/linux_personality/abi/linux_capability_matrix.spl` are the right
  place to map Node-like syscalls and CLI permissions to SimpleOS grants.
- Network/TLS surface:
  `src/os/drivers/virtio/network_device.spl`, `src/os/kernel/net/tls_shim.spl`,
  `src/os/tls12/**`, and `src/os/tls13/**` provide protocol building blocks
  for HTTPS/API calls.
- QEMU lanes:
  `src/os/qemu_runner_part4.spl` and `src/os/qemu_runner_part5.spl` already
  describe RISC-V, x86, and ARM fs-exec and desktop scenarios with serial
  marker contracts.
- Guest toolchain status:
  `.spipe/simpleos_in_guest_toolchain_execution/state.md` records that full
  in-guest compiler/toolchain execution is still blocked by missing real
  clang/rust payloads and bake enablement. This is a relevant precedent for
  Node/AI CLI packaging.

## Current Gaps

- No dedicated Node.js compatibility layer or documented JavaScript subset.
- No package manifests for Codex, Claude, or Gemini CLI on SimpleOS.
- No QEMU lane explicitly provisions a JS/Node runtime plus an AI CLI smoke.
- Existing browser script handling is not enough for Node APIs such as `fs`,
  `child_process`, `net`, `tls`, `process`, terminal raw mode, npm resolution,
  or credential lookup.
- AI CLI hardening needs explicit denial tests for host escape, ambient
  credential reads, undeclared network access, and unbounded process spawning.
- Browser/WASM GUI support exists in pieces (`common.ui.wasm_hello_gui`,
  browser script renderers, and WASM compiler/runtime tests), but the AI CLI
  Node-compatible contract did not previously state the allowed browser/WASM
  imports, required exports, target matrix, or host-escape denials.

## Recommended Next Local Step

Create a narrow compatibility contract before code changes:

1. Define a `simpleos-node-compat` API matrix.
2. Model each AI CLI as a manifest with required APIs and hardening grants.
3. Add a focused SPipe spec that fails closed for undeclared CLI privileges.
4. Wire that spec to QEMU lane metadata before attempting a full Node port.

## 2026-05-30 Contract Extension

`src/os/ai_cli_js_node_contract.spl` now also contains:

- a Bun-informed Simple JS runtime profile that records a cohesive
  runtime/package/transpile/bundle/test surface while explicitly keeping the
  implementation as a Simple MDSOC capsule instead of a Zig/JavaScriptCore copy;
- a Simple browser WASM GUI contract for `simple-browser`, `host-wm`,
  `simpleos-wm`, `android`, and `ios`;
- fail-closed WASM import checks for `fs`, process, environment, network/TLS,
  and host shell escapes;
- required WASM GUI exports: `simple_app_init`, `simple_app_render`, and
  `simple_app_event`.

The focused SPipe spec now proves these contract gates in addition to the
existing Codex/Claude/Gemini manifest and QEMU marker scenarios.

## 2026-05-30 Browser WASM Execution Gate

`src/lib/common/ui/wasm_hello_gui.spl` now carries the same generated-GUI WASM
import/export contract in the browser-facing artifact path. The executable gate
distinguishes:

- approved browser imports such as `simple_ui.present`, input, image, text, and
  time;
- denied host escapes such as filesystem reads/writes, child process spawning,
  environment reads, network/TLS connects, and host shell access;
- required exports: `simple_app_init`, `simple_app_render`, and
  `simple_app_event`.

This moves the previous AI CLI contract from documentation-only planning into
the shared generated-WASM browser artifact evidence path.

## 2026-05-30 Browser Script Hardening

`src/lib/gc_async_mut/gpu/browser_engine/browser_script_execute.spl` no longer
executes collected script text by writing a temporary `.spl` file and spawning
`bin/simple`. The browser script path now has a deterministic in-process policy:

- inline browser JavaScript may execute only literal `console.log(...)`
  statements in this first hardened slice;
- Node/host escape surfaces (`require`, dynamic import, `process.env`, `fs`,
  child process spawning, network APIs, `rt_process_run`, and `host.shell`) are
  denied before execution;
- external `src=` scripts and unsupported script types are collected but denied;
- denial counts and diagnostics are returned to renderer callers.

This is not a full JS engine yet, but it removes the unsafe host subprocess
boundary and creates a clear fail-closed contract for expanding the Simple JS
engine toward the Node/Bun-like runtime profile.
