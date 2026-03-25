# Test Session Sharing Implementation Plan

**Date:** 2026-03-25
**Status:** Planning
**Scope:** Reusable long-lived test environments for QEMU, containers, services, GUI sessions, and hardware-backed targets
**Related:** `doc/research/shared_test_session_research_2026-03-02.md`

---

## 1. Goal

Reduce repeated environment startup cost in the test runner by reusing long-lived sessions when tests are compatible with sharing.

Target environments:

- QEMU VMs
- Containers
- Long-lived service processes such as webservers and mock backends
- GUI app sessions and browser-like harnesses
- Hardware-backed debug sessions such as OpenOCD and TRACE32
- Simulator-style processes such as GHDL

Non-goal:

- Change default semantics for all tests immediately
- Replace the current runner wholesale
- Share state for tests that are destructive or stateful without an explicit reset policy

---

## 2. Existing State

### 2.1 Relevant current implementation

- Generic file-based daemon infrastructure exists in `src/lib/nogc_sync_mut/daemon_sdk/`
- Test daemon exists in `src/app/test_daemon/`
- QEMU broker skeleton exists in `src/app/test_daemon/qemu_broker.spl`
- QEMU grouping exists in `src/lib/nogc_sync_mut/test_runner/qemu_test_runner.spl`
- Test classification exists in `src/lib/nogc_sync_mut/test_runner/test_classification.spl`
- Composite execution paths exist in `src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl`
- Container execution backend exists in `src/lib/nogc_sync_mut/test_runner/test_runner_container.spl`

### 2.2 What already works

- Change-detection cache for test files
- Parallel execution for normal test files
- QEMU test classification into read-only, mutating, and destructive groups
- Generic daemon lifecycle and request/response handling
- Explicit `simple test-daemon start|stop|status`

### 2.3 Main gaps

- `simple test` does not route through the test daemon
- No session-sharing CLI or config switch
- Test daemon still shells out to `bin/simple test <path>` per request
- QEMU broker tracks metadata only; it does not own a real live VM session lifecycle yet
- Container sequential mode is parsed but disabled
- Container backend is one fresh `docker/podman run --rm` per test
- GUI routing tests reference functions that are not present in the current daemon implementation

Conclusion:

The repo has reusable pieces, but session reuse is not yet a real end-to-end feature.

---

## 3. Design Principles

### 3.1 One broker, many adapters

Do not add separate pooling systems for QEMU, containers, GUI, and hardware.

Instead:

- one session broker in the test daemon
- one adapter interface per environment kind
- one scheduler path from the test runner

### 3.2 Resource lifetime and isolation lifetime are separate

Keep expensive resources alive while still providing isolation by:

- snapshot/restore
- reset hooks
- process restart inside the same outer session
- per-test subcontexts

### 3.3 Conservative rollout

Default policy at first:

- no sharing unless enabled by metadata or CLI/config
- destructive tests remain fresh-per-test
- fall back to current execution path on any adapter failure

---

## 4. Session Model

### 4.1 Session kinds

- `qemu_vm`
- `container_instance`
- `service_process`
- `gui_session`
- `browser_session`
- `openocd_board`
- `trace32_board`
- `simulator_process`

### 4.2 Reuse modes

- `shared_read_only`
- `shared_with_reset`
- `shared_with_snapshot`
- `exclusive_reused`
- `fresh_per_test`

### 4.3 Reset policies

- `none`
- `soft_reset`
- `hard_reset`
- `reload_binary`
- `snapshot_restore`
- `recreate`

### 4.4 Session key

Session identity must be based on runtime-relevant inputs, not just test path.

Session key components:

- session kind
- target
- artifact hash
- environment profile
- reuse mode
- reset policy

Examples:

- QEMU: architecture + ELF hash + snapshot policy
- Container: image digest + runtime + network mode + workspace profile
- Service: startup command hash + config hash + port profile
- Hardware: board target + firmware hash + debug backend

---

## 5. Architecture

### 5.1 Control plane

Owned by test daemon:

- session descriptor creation
- lease acquire/release
- scheduling
- health checks
- idle cleanup
- status reporting
- per-kind concurrency limits

### 5.2 Data plane

Owned by adapters:

- start environment
- execute test inside environment
- reset environment
- snapshot and restore
- stop environment

### 5.3 Core daemon components

Proposed new modules:

- `src/app/test_daemon/session_types.spl`
- `src/app/test_daemon/session_broker.spl`
- `src/app/test_daemon/session_adapter.spl`
- `src/app/test_daemon/session_scheduler.spl`
- `src/app/test_daemon/adapters/qemu_adapter.spl`
- `src/app/test_daemon/adapters/container_adapter.spl`
- `src/app/test_daemon/adapters/service_adapter.spl`
- `src/app/test_daemon/adapters/openocd_adapter.spl`
- `src/app/test_daemon/adapters/trace32_adapter.spl`

### 5.4 Adapter interface

Each adapter should support:

- `can_handle(test_meta) -> bool`
- `session_key(test_meta) -> text`
- `start(descriptor) -> runtime`
- `health(runtime) -> bool`
- `reset(runtime, policy) -> Result`
- `execute(runtime, request) -> TestResult`
- `snapshot_create(runtime, name) -> Result`
- `snapshot_restore(runtime, name) -> Result`
- `stop(runtime) -> Result`

---

## 6. Test Metadata

Extend current marker-based classification with explicit session metadata.

Possible file header markers:

```simple
# @session-kind: qemu_vm
# @target: riscv32
# @reuse: shared_with_snapshot
# @reset: snapshot_restore
# @artifact: build/my_test.elf
```

Service example:

```simple
# @session-kind: service_process
# @target: local_web
# @startup: examples/web/server.spl
# @healthcheck: http://127.0.0.1:8080/health
# @reuse: shared_read_only
```

Container example:

```simple
# @session-kind: container_instance
# @target: simple-test-isolation:latest
# @reuse: exclusive_reused
# @reset: recreate
```

Hardware example:

```simple
# @session-kind: trace32_board
# @target: stm32h7
# @reuse: shared_with_reset
# @reset: hard_reset
```

---

## 7. CLI and Config

### 7.1 CLI

Add:

- `--session-share`
- `--no-session-share`
- `--session-daemon`
- `--session-kind=<kinds>`
- `--max-sessions=<n>`
- `--session-debug`
- `--session-reset=<policy>`

Keep:

- `simple test-daemon start`
- `simple test-daemon stop`
- `simple test-daemon status`

Extend status later with verbose broker state.

### 7.2 Config

Add to `config/simple.test.sdn`:

```sdn
session_share: false
session_daemon: false
session_idle_timeout_ms: 300000
session_startup_timeout_ms: 60000

max_sessions:
  qemu_vm: 4
  container_instance: 2
  service_process: 8
  openocd_board: 1
  trace32_board: 1
  simulator_process: 2
```

Per-kind defaults:

```sdn
session_defaults:
  qemu_vm:
    reuse: shared_with_snapshot
    reset: snapshot_restore
  container_instance:
    reuse: exclusive_reused
    reset: recreate
  service_process:
    reuse: shared_read_only
    reset: none
```

---

## 8. Phased Implementation

### Phase 1: Wire the control path

Deliverables:

- Add session-sharing options to test runner args
- Add config parsing for session-sharing
- Add broker skeleton and generic session types
- Route eligible tests from `simple test` into daemon path when enabled
- Preserve fallback to current execution on failure

Success criteria:

- User can opt into session-aware mode
- Non-session tests continue to work unchanged
- Daemon path is exercised by `simple test`, not only MCP tools

### Phase 2: Real QEMU pooled sessions

Deliverables:

- Replace metadata-only QEMU broker behavior with real runtime ownership
- Store actual PID, QMP socket, snapshot state, and health
- Use artifact hash rather than empty binary path
- Implement read-only, mutating, and destructive modes end-to-end

Success criteria:

- Same-arch compatible QEMU tests reuse a live VM
- Mutating tests reset via snapshot restore
- Destructive tests still get fresh sessions
- QEMU startup count drops materially on grouped runs

### Phase 3: Re-enable container mode properly

Deliverables:

- Re-enable session-aware container execution path
- Replace `run --rm` reuse model with create/start plus `exec`
- Add per-container reset policy support
- Add health and cleanup handling

Success criteria:

- Session-capable container tests stop paying full container startup per test
- Disabled container code paths are removed or fully restored

### Phase 4: Hardware-backed sessions

Deliverables:

- OpenOCD adapter
- TRACE32 adapter
- Exclusive lease semantics
- Reset and reconnect policies

Success criteria:

- Board-backed test groups reuse a single connection when safe
- Max sessions per board/backend can be enforced

### Phase 5: Services and GUI

Deliverables:

- Service process adapter
- GUI session adapter
- Browser-like session adapter if needed
- Shared health checks and per-test cleanup hooks

Success criteria:

- webserver/container/gui style integration tests can reuse started environments
- headless and native GUI modes are consistently classified and routed

---

## 9. Priority Order

Implement in this order:

1. daemon wiring into `simple test`
2. real QEMU adapter and broker
3. container pooled sessions
4. OpenOCD and TRACE32
5. services and GUI

Reason:

- QEMU already has the most scaffolding and best ROI
- container support exists but is disabled and single-use
- hardware sessions are valuable but operationally riskier
- service and GUI sessions need policy work more than low-level plumbing

---

## 10. Risks

### 10.1 State leakage

Mitigation:

- opt-in metadata
- explicit reset policy
- destructive tests forced fresh

### 10.2 Dead sessions and stale leases

Mitigation:

- adapter health checks
- lease timeout
- heartbeat for long-running jobs
- broker cleanup on idle timeout

### 10.3 Incorrect session keying

Mitigation:

- include artifact hash and environment profile in key
- do not key only on path or architecture

### 10.4 Scheduler complexity

Mitigation:

- one broker
- one adapter interface
- no environment-specific logic in the runner beyond classification

---

## 11. Initial Success Metrics

- QEMU test suite startup count reduced by at least 50% for compatible grouped runs
- No regression for default `simple test`
- Session-sharing mode can be disabled globally or per run
- Destructive tests remain isolated
- Status output reports active and idle sessions by kind

---

## 12. Immediate Next Tasks

1. Add session-sharing flags and config support
2. Add generic session types and broker skeleton
3. Route session-capable tests from `test_runner_main.spl` into daemon-backed execution
4. Replace the current QEMU broker placeholder behavior with a real adapter
5. Add focused system tests for:
   - QEMU shared read-only
   - QEMU shared with snapshot
   - destructive fresh-per-test
   - daemon fallback to direct execution

---

## 13. Decision

Adopt a generic session broker plus per-environment adapters.

Do not continue expanding environment-specific special cases directly inside the main test runner. The current codebase already has enough partial infrastructure to justify a unified daemon-owned session model.
