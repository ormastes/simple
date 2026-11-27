# Caret Suite + Simple Orchestrator + Simple Container + `agy` Acceptance Manual

**Executable Specification:** `test/03_system/app/orchestrator/feature/caret_orchestrator_container_agy_acceptance_spec.spl`  
**Requirements Covered:** `REQ-ORCH-CARET-AGY-001`, `REQ-ORCH-CARET-AGY-002`, `REQ-ORCH-CARET-AGY-003`, `SC-MAC-001`, `SC-MAC-005`

## Overview

Verifies end-to-end same-host orchestration where Caret Suite (`cs`) starts and communicates with Simple Orchestrator (`caret-serve` / `caret-client`) using a dummy `host.sdn` + `servers.sdn` configuration, launches `agy` inside a VM-free macOS Seatbelt Simple Container (`macos-seatbelt`) attached to an isolated git worktree (`--worktree`), enforces cleanup of worktrees and temporary files on clean close, and preserves crashed containers and worktrees for listing and relaunch.

## Scenarios

### 1. Same-Host Dummy Config, Containerized `agy` Hello-World, and Clean Close Cleanup (`REQ-ORCH-CARET-AGY-001`, `REQ-ORCH-CARET-AGY-002`)

1. **Verify dummy `host.sdn` -> `servers.sdn` resolution:** Both `orchestrator` (server) and `caret` (client) resolve to `same-host` (`transport: "local"`).
2. **Launch Simple Orchestrator server through Caret Suite:** `/orchestrator start --runtime-dir <dir>` initializes the WAL-backed Orchestrator Controller (`controller.sdn` + `journal/database-wal/CURRENT`) and binds a loopback TCP listener (`127.0.0.1:<port>`) authenticated with a per-instance CSPRNG token.
3. **Launch `agy` with `macos-seatbelt` container and `--worktree`:** `/orchestrator launch agy --container macos-seatbelt --worktree -p "Reply with the exact word HELLO_WORLD and nothing else."` records the workload in the controller journal, creates a detached git worktree, compiles the Seatbelt SBPL profile, and spawns `agy` inside `/usr/bin/sandbox-exec -f <profile.sb>`.
4. **Prove Seatbelt write confinement:** Writing to `<repo_dir>/forbidden.txt` is denied by the Darwin kernel while writing inside `<worktree_path>` succeeds.
5. **Observe hello-world completion and clean close:** After `HELLO_WORLD` is captured and the container reaches `exited-clean` (`exitCode: 0`), `/orchestrator close a1` removes the detached git worktree, container attempt directory, pane launcher script, and stderr spool, and `/orchestrator stop` removes the server state root leaving zero leftover worktrees or temporary files.

### 2. Crash Retention, Crashed-Container Listing, and Relaunch in Preserved Worktree (`REQ-ORCH-CARET-AGY-003`)

1. **Crash preserves worktree and container state:** Launching `agy` inside `macos-seatbelt` with `--worktree` and an invalid flag exits nonzero (`state: "crashed"`). Uncommitted files inside `<worktree_path>` (`wip_preserved.txt`) and `<attempt_dir>/session.sdn` remain intact even when `/orchestrator close a1` is called (`preservedForRelaunch: true`).
2. **List crashed containers:** `/orchestrator crashed` (and Caret Suite `/containers` / `/crashed`) reports `crashedCount: 1` with the container name and preserved `worktreePath`.
3. **Relaunch to clean completion and cleanup:** `/orchestrator relaunch a1 -p "Reply with the exact word HELLO_WORLD and nothing else."` resumes `agy` inside the preserved `worktreePath` (retaining `wip_preserved.txt`), captures `HELLO_WORLD` (`exited-clean`), and `/orchestrator close a1` + `/orchestrator stop` then delete the worktree and all temporary files completely.
