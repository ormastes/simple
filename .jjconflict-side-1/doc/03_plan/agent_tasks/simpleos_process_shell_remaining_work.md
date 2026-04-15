# SimpleOS Process-Shell Remaining Work

## Scope

This document captures the remaining work after the first process-first shell integration pass on the real SimpleOS desktop path.

Current baseline already implemented:
- launcher owns process registry and launch state
- WM/compositor carry `process_id` and `app_id` metadata
- shell renders a process panel and a separate visible-window surface
- non-headless QEMU GUI runs suppress serial boot logs

This plan covers what is still needed to make the feature production-ready on the SimpleOS path using the MDSOC boundary:
- launcher layer owns process truth
- WM/compositor layer owns window truth
- shell layer renders joined read-only views
- CLI/QEMU tooling owns build/run orchestration

## Remaining Gaps

### 1. Real process identity join for remote windows

Current state:
- WM action parsing still defaults `process_id` from `src_port`
- `app_id` fallback still uses `title`

Why it matters:
- shell grouping is structurally correct, but it is not yet joined to launcher-owned PID truth for all remote app paths

Required update:
- define a stable app/window identity handshake between launcher-spawned processes and WM create-window IPC
- prefer real PID or launcher-issued process handle over IPC-port-derived synthetic identity
- use app manifest identity for `app_id`, not window title

Files likely involved:
- `src/os/services/wm/wm_service.spl`
- `src/os/services/launcher/launcher.spl`
- `src/os/userlib/**`
- `src/common/window_protocol/**`

Acceptance:
- a launched app with multiple windows resolves to one process identity
- relabeling a window title does not change taskbar/process grouping
- window ownership queries match launcher process snapshots

### 2. Process exit and crash propagation

Current state:
- launcher supports exit-state storage
- shell updates window counts on create/destroy
- there is no end-to-end event path proving exit/crash cleanup from real app termination back into shell/WM state

Required update:
- add or complete exit notification flow from runtime/kernel/process supervisor into launcher
- remove or mark windows for dead processes when the owner exits unexpectedly
- distinguish `exited`, `crashed`, and `terminated`

Files likely involved:
- `src/os/services/launcher/launcher.spl`
- `src/os/services/wm/wm_service.spl`
- `src/os/compositor/compositor.spl`
- desktop entry/test harness files

Acceptance:
- process panel state changes without manual refresh logic
- orphaned windows are removed or marked invalid after owner death
- graceful close and forced terminate stay separate behaviors

### 3. Shell process manager actions

Current state:
- shell renders process rows
- panel is read-only

Required update:
- add process actions:
  - focus first window
  - terminate process
  - optionally relaunch exited app
- keep taskbar/window list window-first
- keep process panel process-first

Files likely involved:
- `src/os/desktop/shell.spl`
- compositor input routing / UI helpers
- launcher terminate/relaunch APIs

Acceptance:
- user can terminate a process from shell UI
- focus action targets owned windows, not just title matches
- headless processes remain visible in process panel only

### 4. Replace overlay/demo shortcuts with manifest-driven desktop state

Current state:
- baremetal overlay still uses a simplified demo list for launcher tiles
- visible fake windows are derived from launcher window counts, which is better, but still a demo path

Required update:
- connect launcher grid and app launch metadata to loaded app manifests
- render icons/names from manifest data
- stop relying on hardcoded demo app lists for the main desktop lane

Files likely involved:
- `src/os/desktop/shell.spl`
- `src/os/desktop/app_manifest.spl`
- example desktop entrypoints

Acceptance:
- desktop launcher contents come from manifests
- visible window labels and process labels use consistent app identity

### 5. QEMU GUI/headless logging policy refinement

Current state:
- GUI mode uses `-serial none`
- headless mode keeps serial output

Risk:
- GUI debugging is now harder when serial is fully suppressed

Required update:
- preserve Mac-like GUI startup by default
- add an explicit debug lane or flag that keeps GUI window plus serial capture
- ensure tests that require serial assertions do not accidentally run through silent GUI mode

Files likely involved:
- `src/os/qemu_runner.spl`
- OS CLI command dispatch
- docs for QEMU run modes

Acceptance:
- normal GUI run stays quiet
- debug GUI run exposes serial output in a deliberate way
- test lanes stay deterministic

### 6. Fix `bin/simple os` CLI wrapper path

Current state:
- `bin/simple os targets` exits `3` with no output
- `bin/simple os build --arch=x86_64` exits `3` with no output
- direct `bin/simple native-build ...` succeeds for the kernel and desktop entries

Interpretation:
- feature code compiles
- the broken layer is the `os` subcommand path, not the desktop implementation

Required update:
- inspect and fix CLI dispatch/runtime for `os` subcommands
- ensure `os targets` and `os build` surface actionable diagnostics on failure
- add regression coverage for the wrapper path

Files likely involved:
- CLI dispatch files under `app/cli/**` or equivalent command entry path
- `src/os/qemu_runner.spl` only if command contract changed

Acceptance:
- `bin/simple os targets` returns a usable target list
- `bin/simple os build --arch=x86_64` succeeds or emits explicit diagnostics

## Parallel Work Breakdown

### Agent A: Launcher and runtime

Ownership:
- `src/os/services/launcher/**`
- runtime/process exit bridge

Tasks:
- complete exit/crash propagation
- expose stable process identity for WM join
- verify terminate semantics

### Agent B: WM and protocol

Ownership:
- `src/os/services/wm/**`
- `src/common/window_protocol/**`
- `src/os/userlib/**`

Tasks:
- replace synthetic `src_port`/title defaults with real process/app identity
- verify multi-window ownership grouping

### Agent C: Shell and desktop UX

Ownership:
- `src/os/desktop/shell.spl`
- desktop entrypoints

Tasks:
- add process panel actions
- switch remaining demo state to manifest-backed desktop data
- keep taskbar/window list separate from process panel

### Agent D: QEMU and CLI orchestration

Ownership:
- `src/os/qemu_runner.spl`
- CLI dispatch path for `bin/simple os`

Tasks:
- preserve quiet GUI default
- add explicit debug lane
- fix `os` wrapper failure and diagnostics

### Agent E: Verification

Ownership:
- specs and test harnesses only

Tasks:
- add regression coverage for process/window identity
- add exit/crash cleanup checks
- add CLI wrapper coverage for `os targets` and `os build`

## Recommended Execution Order

1. Fix `bin/simple os` wrapper so the normal build/run path is trustworthy again.
2. Implement the real WM/launcher identity join.
3. Complete exit/crash propagation and stale-window cleanup.
4. Add shell process actions.
5. Refine QEMU run/debug mode split.
6. Replace remaining hardcoded desktop demo state with manifest-backed data.
7. Run full verification on direct `native-build` and `os build` paths.

## Verification Matrix

### Unit

- launcher process state transitions
- WM ownership identity queries
- compositor window identity queries

### Integration

- launch app -> process row appears
- create window -> taskbar/window list and process panel both update
- destroy window -> window count decrements
- terminate process -> process removed and windows cleaned up

### QEMU

- GUI run stays quiet by default
- headless run shows serial output
- debug GUI lane preserves serial visibility when requested

### CLI

- `bin/simple os targets`
- `bin/simple os build --arch=x86_64`
- failure cases return explicit diagnostics

## Definition Of Done

- real launcher process identity reaches WM/compositor/shell end-to-end
- process exit/crash cleanup is automatic
- shell process panel is actionable, not read-only
- GUI startup is quiet by default but debuggable on demand
- `bin/simple os` wrapper works again
- direct `native-build` and wrapper `os build` both pass for the desktop lane
