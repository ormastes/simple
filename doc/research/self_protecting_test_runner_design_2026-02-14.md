# Self-Protecting Test Runner with Resource Daemon - Research & Design

**Date:** 2026-02-14
**Status:** Research & Design Phase
**Author:** Claude Sonnet 4.5
**Priority:** HIGH (Production Infrastructure)

---

## Executive Summary

Design a **self-protecting test runner** that monitors its own resource usage and enforces system-wide resource limits through a shared daemon. When memory or CPU exceeds 80% threshold, the runner kills itself, all child processes, and containers, then restarts when resources become available.

**Key Features:**
1. **Self-monitoring:** Test runner tracks its own CPU/memory usage
2. **80% threshold enforcement:** Kill self + children when limits exceeded
3. **Graceful shutdown:** Clean up processes, containers, ports, temp files
4. **Shared daemon:** System-wide resource coordinator
5. **Automatic restart:** Resume testing when resources available
6. **Port management:** Track and clean up hung ports
7. **Container lifecycle:** Track and kill containers on shutdown

**Use Cases:**
- **CI/CD environments:** Prevent runaway tests from hanging CI pipelines
- **Resource-constrained systems:** Laptops, VMs with limited RAM
- **Long-running test suites:** Multi-hour runs that could leak resources
- **Parallel execution:** Multiple test runners competing for resources

---

## Problem Statement

### Current Limitations

**1. No Self-Protection:**
- Test runner can consume unlimited resources
- Runaway tests can exhaust system memory/CPU
- No way to detect when runner itself is the problem

**2. No Graceful Shutdown:**
- SIGTERM/SIGINT may leave orphaned processes
- Containers not cleaned up on abnormal exit
- Port conflicts from hung processes

**3. No Coordination:**
- Multiple test runners don't share resource awareness
- Each runner operates independently
- No system-wide resource management

**4. No Automatic Recovery:**
- Manual intervention required after resource exhaustion
- No restart mechanism
- Lost test progress

### Real-World Scenarios

**Scenario 1: Memory Leak in Test**
```
Time 0:00 - Test runner starts (200 MB)
Time 1:00 - Test leaks memory, runner at 2 GB
Time 1:30 - System OOM killer terminates runner
Result: All progress lost, no cleanup, orphaned processes
```

**Desired Behavior:**
```
Time 0:00 - Test runner starts (200 MB)
Time 1:00 - Test leaks memory, runner at 2 GB (80% threshold)
Time 1:01 - Runner detects violation, saves progress
Time 1:02 - Runner kills self + children, cleans up containers
Time 1:03 - Daemon detects resource availability
Time 1:04 - Runner restarts from checkpoint
Result: Automatic recovery, clean shutdown, progress saved
```

**Scenario 2: Hung Port from Test**
```
Test opens port 8080, crashes without cleanup
Port 8080 remains open by orphaned process
Next test run fails: "Address already in use"
```

**Desired Behavior:**
```
Daemon tracks port 8080 opened by PID 12345
Test runner exits abnormally
Daemon detects orphan process, kills PID 12345
Port 8080 released automatically
Next test run succeeds
```

---

## Architecture Overview

### Three-Tier Architecture

```
┌─────────────────────────────────────────────────────────┐
│                    System Layer                          │
│  ┌─────────────────────────────────────────────────┐   │
│  │  Resource Daemon (simple-test-daemon)           │   │
│  │  - System-wide resource monitoring              │   │
│  │  - Port tracking and cleanup                    │   │
│  │  - Restart coordination                         │   │
│  │  - IPC server (Unix socket)                     │   │
│  └─────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────┘
                          ↑ IPC
┌─────────────────────────────────────────────────────────┐
│                 Test Runner Layer                        │
│  ┌─────────────────────────────────────────────────┐   │
│  │  Self-Protecting Test Runner                    │   │
│  │  - Self resource monitoring (CPU, memory)       │   │
│  │  - Threshold detection (80% limit)              │   │
│  │  - Graceful shutdown coordination               │   │
│  │  - Progress checkpointing                       │   │
│  │  - Daemon registration                          │   │
│  └─────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────┘
                          ↑ Process Control
┌─────────────────────────────────────────────────────────┐
│                Execution Layer                           │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐ │
│  │ Test Process │  │  Container   │  │   Ports      │ │
│  │  (child)     │  │ (docker/pod) │  │  (8080, ..)  │ │
│  └──────────────┘  └──────────────┘  └──────────────┘ │
└─────────────────────────────────────────────────────────┘
```

---

## Component Design

### 1. Resource Daemon (`simple-test-daemon`)

**Purpose:** System-wide resource monitoring and coordination daemon.

**Responsibilities:**
- Monitor system CPU/memory availability
- Track all test runner instances
- Manage port allocation and cleanup
- Coordinate restarts after resource exhaustion
- Provide IPC API for test runners

**Implementation:** `src/app/test_daemon/`

#### 1.1 Daemon Core

**File:** `src/app/test_daemon/daemon_core.spl`

```simple
struct DaemonState:
    pid: i64
    socket_path: text
    runners: [RunnerInfo]
    ports: [PortInfo]
    system_stats: SystemStats
    last_cleanup_ms: i64

struct RunnerInfo:
    pid: i64
    start_time_ms: i64
    cpu_percent: f64
    memory_mb: i64
    status: text  # "running", "shutdown", "waiting_restart"
    checkpoint_path: text
    ports_owned: [i64]

struct PortInfo:
    port: i64
    owner_pid: i64
    opened_at_ms: i64
    protocol: text  # "tcp", "udp"

struct SystemStats:
    total_cpu_percent: f64
    total_memory_mb: i64
    available_memory_mb: i64
    load_average: f64

fn daemon_start() -> i64:
    # Start daemon process
    # Returns daemon PID

fn daemon_main_loop():
    # Main event loop
    # - Monitor system resources every 1s
    # - Check runner health every 5s
    # - Cleanup orphaned processes/ports every 10s
    # - Coordinate restarts

fn daemon_monitor_system() -> SystemStats:
    # Read /proc/meminfo, /proc/stat, /proc/loadavg
    # Calculate system-wide usage

fn daemon_cleanup_orphans():
    # Find processes without parent
    # Find containers without runner
    # Find ports without process
    # Kill and cleanup

fn daemon_coordinate_restart(runner_pid: i64) -> bool:
    # Check if resources available (< 70% threshold)
    # Send restart signal to runner
    # Update runner state
```

#### 1.2 IPC Server

**File:** `src/app/test_daemon/daemon_ipc.spl`

**Protocol:** Unix domain socket (text-based protocol)

```simple
struct DaemonMessage:
    type: text  # "register", "heartbeat", "report_port", "request_shutdown", "ack"
    runner_pid: i64
    data: text  # JSON-like payload

# IPC Commands
fn ipc_register_runner(pid: i64, checkpoint_path: text) -> text:
    # Register new test runner
    # Returns: "ok" or "error: <reason>"

fn ipc_heartbeat(pid: i64, cpu: f64, memory: i64) -> text:
    # Update runner stats
    # Returns: "ok", "shutdown" (if over threshold), "restart"

fn ipc_report_port(pid: i64, port: i64, protocol: text) -> text:
    # Register port ownership
    # Returns: "ok" or "conflict: <owner_pid>"

fn ipc_release_port(pid: i64, port: i64) -> text:
    # Release port ownership
    # Returns: "ok"

fn ipc_request_shutdown(pid: i64) -> text:
    # Request graceful shutdown (runner initiating)
    # Returns: "ok"

fn ipc_query_status() -> text:
    # Query daemon status
    # Returns: JSON with system stats, runners, ports
```

**Socket Path:** `/tmp/simple-test-daemon.sock` (or `$XDG_RUNTIME_DIR/simple-test-daemon.sock`)

#### 1.3 Port Manager

**File:** `src/app/test_daemon/port_manager.spl`

```simple
fn port_manager_track(port: i64, pid: i64, protocol: text):
    # Register port ownership

fn port_manager_release(port: i64, pid: i64):
    # Release port

fn port_manager_find_orphans() -> [(i64, i64)]:
    # Find ports owned by dead processes
    # Returns: [(port, old_pid)]

fn port_manager_kill_port(port: i64) -> bool:
    # Find process using port and kill it
    # Uses: lsof -ti:PORT | xargs kill -9

fn port_manager_is_available(port: i64) -> bool:
    # Check if port is free
```

**Port Tracking:**
- Test runner reports port opens to daemon
- Daemon maintains port→PID mapping
- On runner exit, daemon closes all owned ports
- Periodic cleanup finds orphaned ports

---

### 2. Self-Protecting Test Runner

**Purpose:** Test runner that monitors its own resource usage and shuts down gracefully when limits exceeded.

**Implementation:** `src/app/test_runner_new/self_protection.spl`

#### 2.1 Self-Monitoring Thread

```simple
struct SelfMonitorConfig:
    enabled: bool
    cpu_threshold_percent: f64     # 80% default
    memory_threshold_mb: i64       # System dependent
    check_interval_ms: i64         # 1000ms (1 second)
    daemon_socket: text
    checkpoint_path: text

fn self_monitor_start(config: SelfMonitorConfig) -> i64:
    # Spawn monitoring thread
    # Returns: monitor thread PID

fn self_monitor_loop(config: SelfMonitorConfig):
    while true:
        # 1. Sample self metrics
        val my_pid = getpid()
        val metrics = sample_process(my_pid, time_now_ms())

        # 2. Send heartbeat to daemon
        val response = ipc_heartbeat(my_pid, metrics.cpu_percent, metrics.memory_mb)

        # 3. Check daemon response
        if response == "shutdown":
            # Daemon says we're over threshold
            initiate_graceful_shutdown()
            break

        # 4. Local threshold check (fallback if daemon unavailable)
        if metrics.cpu_percent > config.cpu_threshold_percent:
            print "[SELF-PROTECTION] CPU exceeded {config.cpu_threshold_percent}%"
            initiate_graceful_shutdown()
            break

        if metrics.memory_mb > config.memory_threshold_mb:
            print "[SELF-PROTECTION] Memory exceeded {config.memory_threshold_mb} MB"
            initiate_graceful_shutdown()
            break

        # 5. Sleep until next check
        sleep_ms(config.check_interval_ms)
```

#### 2.2 Graceful Shutdown

```simple
struct ShutdownContext:
    reason: text  # "cpu_limit", "memory_limit", "daemon_request"
    checkpoint_path: text
    test_results_so_far: [TestFileResult]
    current_test_file: text
    child_pids: [i64]
    containers: [text]
    ports: [i64]

fn initiate_graceful_shutdown():
    print "[SHUTDOWN] Initiating graceful shutdown..."

    # 1. Save progress checkpoint
    val checkpoint = create_checkpoint()
    save_checkpoint(checkpoint)

    # 2. Kill all child processes (test executions)
    kill_all_children()

    # 3. Stop all containers
    cleanup_all_containers()

    # 4. Release all ports
    release_all_ports()

    # 5. Notify daemon
    ipc_request_shutdown(getpid())

    # 6. Exit cleanly
    exit(42)  # Special code for "graceful resource shutdown"

fn create_checkpoint() -> Checkpoint:
    # Save current test runner state
    # - Which tests completed
    # - Which test was running when shutdown
    # - Test results so far
    # - Configuration/options

fn save_checkpoint(checkpoint: Checkpoint):
    # Write to: .simple-test-checkpoint.sdn
    # Format: SDN for human readability

fn restore_from_checkpoint(path: text) -> Checkpoint:
    # Load checkpoint and resume
```

#### 2.3 Child Process Tracking

```simple
struct ProcessTree:
    runner_pid: i64
    child_pids: [i64]
    container_ids: [text]

fn track_child_spawn(pid: i64):
    # Register child process

fn track_container_start(container_id: text):
    # Register container

fn kill_all_children():
    # Send SIGTERM to all children
    # Wait 5 seconds
    # Send SIGKILL to survivors

fn cleanup_all_containers():
    # docker stop <container_id>
    # docker rm <container_id>
```

---

### 3. Resource Monitoring Integration

**Extend existing `src/lib/process_monitor.spl`:**

#### 3.1 System-Wide Monitoring

```simple
fn monitor_system_resources() -> SystemStats:
    # Read system-wide metrics (not just one process)
    # Linux: /proc/meminfo, /proc/stat
    # macOS: sysctl, vm_stat
    # Windows: wmic

struct SystemStats:
    total_cpu_percent: f64      # 0-100 per core (400% on 4-core)
    used_memory_mb: i64
    total_memory_mb: i64
    available_memory_mb: i64
    load_average_1m: f64
    load_average_5m: f64
    load_average_15m: f64

fn system_memory_percent() -> f64:
    val stats = monitor_system_resources()
    val used = stats.used_memory_mb
    val total = stats.total_memory_mb
    (used / total) * 100.0

fn system_cpu_percent() -> f64:
    # Average CPU usage across all cores
    val stats = monitor_system_resources()
    stats.total_cpu_percent / cpu_count()
```

#### 3.2 Threshold Calculation

```simple
fn calculate_thresholds(config: SelfMonitorConfig) -> (f64, i64):
    # Calculate absolute thresholds from percentages
    val sys_stats = monitor_system_resources()

    # Memory threshold: 80% of total system memory
    val memory_threshold_mb = (sys_stats.total_memory_mb * 80) / 100

    # CPU threshold: 80% of available CPU (per-core)
    val cpu_threshold_percent = 80.0 * cpu_count()

    (cpu_threshold_percent, memory_threshold_mb)

fn cpu_count() -> i64:
    # Linux: /proc/cpuinfo | grep processor | wc -l
    # macOS: sysctl -n hw.ncpu
    # Windows: wmic cpu get NumberOfCores
```

---

## Implementation Plan

### Phase 1: Daemon Foundation (Week 1)

**Day 1-2: Daemon Core**
- [ ] `src/app/test_daemon/daemon_core.spl` - Main daemon logic
- [ ] System-wide resource monitoring
- [ ] Runner registry (in-memory)
- [ ] Main event loop
- [ ] Tests: 15+ test cases

**Day 3: IPC Server**
- [ ] `src/app/test_daemon/daemon_ipc.spl` - Unix socket server
- [ ] Message protocol implementation
- [ ] Client library for test runner
- [ ] Tests: 10+ test cases

**Day 4: Port Manager**
- [ ] `src/app/test_daemon/port_manager.spl` - Port tracking
- [ ] Orphan detection
- [ ] Port cleanup
- [ ] Tests: 8+ test cases

**Deliverables:**
- Daemon that runs as background process
- IPC API for registration/heartbeat
- Port tracking and cleanup
- 33+ tests passing

---

### Phase 2: Self-Protection (Week 2)

**Day 1-2: Self-Monitoring**
- [ ] `src/app/test_runner_new/self_protection.spl` - Self-monitor thread
- [ ] Resource threshold detection
- [ ] Daemon integration
- [ ] Tests: 12+ test cases

**Day 3: Graceful Shutdown**
- [ ] Checkpoint save/restore
- [ ] Child process killing
- [ ] Container cleanup
- [ ] Port release
- [ ] Tests: 15+ test cases

**Day 4: Integration**
- [ ] Modify `test_runner_main.spl` to use self-protection
- [ ] CLI flags: `--self-protect`, `--threshold=N`
- [ ] End-to-end testing
- [ ] Tests: 10+ test cases

**Deliverables:**
- Test runner with self-monitoring
- Graceful shutdown on threshold violation
- Checkpoint/restore functionality
- 37+ tests passing

---

### Phase 3: Automatic Restart (Week 3)

**Day 1: Restart Coordinator**
- [ ] `src/app/test_daemon/restart_coordinator.spl` - Restart logic
- [ ] Resource availability detection
- [ ] Runner respawn
- [ ] Tests: 10+ test cases

**Day 2: Checkpoint Resume**
- [ ] Resume from checkpoint
- [ ] Skip completed tests
- [ ] Continue from interrupted test
- [ ] Tests: 12+ test cases

**Day 3: Production Hardening**
- [ ] Daemon auto-start (systemd, launchd)
- [ ] Logging and diagnostics
- [ ] Configuration files
- [ ] Tests: 8+ test cases

**Day 4: Documentation**
- [ ] User guide
- [ ] Architecture docs
- [ ] Troubleshooting guide

**Deliverables:**
- Automatic restart on resource recovery
- Production-grade daemon
- Complete documentation
- 30+ tests passing

---

## Configuration

### Daemon Configuration

**File:** `/etc/simple-test/daemon.sdn` (or `~/.config/simple-test/daemon.sdn`)

```sdn
daemon {
    socket_path "/tmp/simple-test-daemon.sock"

    # System resource thresholds (daemon will request shutdown)
    cpu_threshold_percent 80.0
    memory_threshold_percent 80.0

    # Monitoring intervals
    system_check_interval_ms 1000
    runner_check_interval_ms 5000
    cleanup_interval_ms 10000

    # Restart policy
    restart_enabled true
    restart_delay_ms 5000
    max_restart_attempts 3

    # Port management
    port_cleanup_enabled true
    port_orphan_timeout_ms 30000

    # Logging
    log_file "/var/log/simple-test-daemon.log"
    log_level "info"  # debug, info, warn, error
}
```

### Test Runner Configuration

**File:** `simple.test.sdn` (project-level)

```sdn
test_config {
    # Self-protection settings
    self_protection {
        enabled true
        cpu_threshold_percent 80.0
        memory_threshold_mb 8192  # 8 GB
        check_interval_ms 1000
    }

    # Checkpoint settings
    checkpoint {
        enabled true
        path ".simple-test-checkpoint.sdn"
        save_interval_tests 10  # Checkpoint every 10 tests
    }

    # Daemon integration
    daemon {
        enabled true
        socket_path "/tmp/simple-test-daemon.sock"
        heartbeat_interval_ms 5000
        register_ports true
    }

    # Graceful shutdown
    shutdown {
        child_kill_timeout_ms 5000
        container_stop_timeout_ms 10000
        checkpoint_on_shutdown true
    }
}
```

---

## Usage Examples

### Basic Usage (Manual)

```bash
# Start daemon (once per system)
simple test-daemon start

# Run tests with self-protection
simple test --self-protect

# Run with custom threshold
simple test --self-protect --cpu-threshold=70

# Check daemon status
simple test-daemon status

# Stop daemon
simple test-daemon stop
```

### Automatic Daemon (systemd)

**File:** `/etc/systemd/system/simple-test-daemon.service`

```ini
[Unit]
Description=Simple Language Test Resource Daemon
After=network.target

[Service]
Type=simple
ExecStart=/usr/local/bin/simple test-daemon start --foreground
Restart=on-failure
User=nobody
Group=nogroup

[Install]
WantedBy=multi-user.target
```

```bash
# Enable daemon on boot
sudo systemctl enable simple-test-daemon
sudo systemctl start simple-test-daemon

# Check status
sudo systemctl status simple-test-daemon
```

### Example Scenario: Graceful Shutdown

```
$ simple test test/integration/ --self-protect

[INFO] Registering with daemon (socket: /tmp/simple-test-daemon.sock)
[INFO] Self-protection enabled (CPU: 80%, Memory: 8192 MB)
[INFO] Running 150 tests...
Running test/integration/database_spec.spl... PASS
Running test/integration/compiler_spec.spl... PASS
...
Running test/integration/heavy_spec.spl...
[WARN] Memory usage: 6500 MB (79% of limit)
[WARN] Memory usage: 6900 MB (84% of limit)
[SHUTDOWN] Memory exceeded threshold (8192 MB)
[SHUTDOWN] Saving checkpoint (.simple-test-checkpoint.sdn)
[SHUTDOWN] Killing 3 child processes...
[SHUTDOWN] Stopping 2 containers...
[SHUTDOWN] Releasing 5 ports...
[SHUTDOWN] Notifying daemon...
[INFO] Graceful shutdown complete. Progress saved.

# Daemon detects resource recovery after 30 seconds
[DAEMON] System memory recovered to 45%
[DAEMON] Restarting test runner from checkpoint...
[INFO] Resuming from checkpoint (completed: 47/150 tests)
Running test/integration/network_spec.spl... PASS
...
```

---

## Port Management Example

### Test Code

```simple
use std.spec.{describe, it}
use app.io.mod.{socket_bind, daemon_register_port}

describe "HTTP server":
    it "starts on port 8080":
        # Register port with daemon
        daemon_register_port(8080, "tcp")

        # Bind socket
        val sock = socket_bind("0.0.0.0", 8080)
        expect(sock.?).to_equal(true)

        # Test logic...

        # Daemon auto-releases on test exit
```

### Daemon Tracking

```
[DAEMON] Runner PID 12345 registered port 8080 (tcp)
[DAEMON] Runner PID 12345 exited
[DAEMON] Checking port 8080... still open by PID 12346 (child)
[DAEMON] Killing orphan process PID 12346
[DAEMON] Port 8080 released
```

---

## Performance Characteristics

### Daemon Overhead

**CPU Usage:**
- Idle: <0.1%
- Active monitoring: ~0.5-1% (1 runner)
- With cleanup: ~2% (peaks during orphan scan)

**Memory Usage:**
- Base: ~5 MB
- Per runner: ~500 KB
- Per port: ~100 bytes

**Disk I/O:**
- /proc reads: ~10 KB/s
- Checkpoint writes: ~10 KB per checkpoint
- Logs: ~1 KB/s (info level)

### Self-Protection Overhead

**CPU:**
- Self-monitoring thread: ~0.2%
- IPC heartbeat: ~0.1%

**Memory:**
- Checkpoint buffer: ~1 MB
- Process tree tracking: ~100 KB

**Total overhead:** <1% CPU, <2 MB RAM

---

## Testing Strategy

### Unit Tests

**Daemon Core:**
- System resource monitoring
- Runner registration/deregistration
- Threshold detection
- Event loop iteration

**IPC Server:**
- Socket creation/binding
- Message parsing
- Command handling
- Error cases

**Port Manager:**
- Port tracking
- Orphan detection
- Port killing
- Conflict detection

**Self-Protection:**
- Threshold calculation
- Self-monitoring loop
- Graceful shutdown
- Checkpoint save/restore

### Integration Tests

**Daemon + Runner:**
- Runner registers with daemon
- Heartbeat exchange
- Threshold violation triggers shutdown
- Port cleanup on exit

**Checkpoint Resume:**
- Save progress mid-run
- Restore and continue
- Skip completed tests
- Handle interrupted test

**Automatic Restart:**
- Daemon detects shutdown
- Waits for resource recovery
- Restarts runner
- Resumes from checkpoint

### End-to-End Tests

**Scenario: Memory Exhaustion**
- Start test runner
- Run memory-leaking test
- Hit 80% threshold
- Graceful shutdown
- Automatic restart
- Complete remaining tests

**Scenario: Port Conflict**
- Test opens port 8080
- Test crashes
- Port remains open
- Daemon detects orphan
- Daemon kills port
- Next test succeeds

**Scenario: Multiple Runners**
- Start 3 test runners
- Each registers with daemon
- One hits threshold
- Daemon shuts down only that runner
- Other runners continue
- Shutdown runner restarts when resources available

---

## Security Considerations

### Daemon Security

**Socket Permissions:**
- Unix socket at `/tmp/simple-test-daemon.sock`
- Permissions: 0600 (owner only)
- Or use `$XDG_RUNTIME_DIR` (user-specific)

**Process Isolation:**
- Daemon runs as current user (not root)
- Can only kill own processes
- Cannot kill other users' processes

**Command Validation:**
- IPC commands validated
- PID ownership checked
- No arbitrary command execution

### Resource Limits

**Prevent Abuse:**
- Daemon itself has resource limits (512 MB, 50% CPU)
- Max 100 runners per daemon
- Max 1000 ports tracked
- Rate limiting on IPC commands (100/sec)

---

## Failure Modes & Recovery

### Daemon Crashes

**Problem:** Daemon exits unexpectedly

**Recovery:**
- Test runner detects socket unavailable
- Switches to local-only self-protection
- Continues without daemon coordination
- Logs warning

### Test Runner Killed (SIGKILL)

**Problem:** Runner killed without graceful shutdown

**Recovery:**
- Daemon detects runner exit (heartbeat timeout)
- Daemon performs cleanup:
  - Kill child processes via PGID
  - Stop containers via container ID registry
  - Release registered ports
- Checkpoint may be incomplete
- Manual intervention may be needed

### Checkpoint Corruption

**Problem:** Checkpoint file corrupted

**Recovery:**
- Detect corruption on load
- Fall back to full test run
- Log warning
- Delete corrupted checkpoint

### Resource Never Recovers

**Problem:** System resources stay above 80% indefinitely

**Recovery:**
- Daemon waits up to 1 hour
- After 1 hour, forcibly restart (may fail again)
- After 3 failed restarts, give up
- Notify user via exit code + log

---

## Metrics & Observability

### Daemon Metrics

**Exposed via:** `simple test-daemon metrics` (JSON output)

```json
{
  "daemon_pid": 12345,
  "uptime_seconds": 3600,
  "runners_active": 2,
  "runners_total": 5,
  "shutdowns_triggered": 3,
  "restarts_successful": 2,
  "ports_tracked": 8,
  "ports_cleaned": 1,
  "system_cpu_percent": 45.5,
  "system_memory_percent": 62.3
}
```

### Test Runner Metrics

**Appended to test output:**

```
--- Resource Usage ---
Self CPU: 85.2% (EXCEEDED THRESHOLD 80%)
Self Memory: 6800 MB (WITHIN THRESHOLD 8192 MB)
Checkpoint saved: .simple-test-checkpoint.sdn
Graceful shutdown: Success
```

### Logs

**Daemon Log:** `/var/log/simple-test-daemon.log`

```
[2026-02-14 10:30:00] INFO Daemon started (PID 12345)
[2026-02-14 10:30:15] INFO Runner registered (PID 12400)
[2026-02-14 10:35:20] WARN Runner 12400 memory: 6500 MB (79%)
[2026-02-14 10:35:25] WARN Runner 12400 memory: 6900 MB (84%)
[2026-02-14 10:35:26] INFO Shutdown requested (runner 12400, reason: memory)
[2026-02-14 10:35:30] INFO Runner 12400 exited gracefully
[2026-02-14 10:35:35] INFO Cleaned 3 child processes, 2 containers, 5 ports
[2026-02-14 10:36:00] INFO System memory recovered (45%)
[2026-02-14 10:36:05] INFO Restarting runner 12400 from checkpoint
```

---

## Alternatives Considered

### Alternative 1: No Daemon (Local Only)

**Pros:**
- Simpler implementation
- No daemon management
- Fewer moving parts

**Cons:**
- No coordination between runners
- Port conflicts not handled
- No automatic restart
- Each runner isolated

**Verdict:** Rejected. Daemon provides critical coordination.

### Alternative 2: systemd-based Limits

**Pros:**
- Uses existing systemd infrastructure
- Native resource limiting (cgroups)
- Automatic restart built-in

**Cons:**
- Linux-only
- Requires root/systemd access
- No graceful checkpoint
- Not portable to macOS/Windows

**Verdict:** Complementary. Can use systemd for daemon, but not for test runner.

### Alternative 3: Kubernetes-based

**Pros:**
- Native resource limits (memory, CPU)
- Automatic restart
- Multi-node orchestration

**Cons:**
- Massive complexity
- Not suitable for local dev
- Over-engineered for single-machine use

**Verdict:** Rejected. Too complex for local testing.

---

## Open Questions

1. **Checkpoint Format:**
   - SDN vs binary?
   - Full state vs minimal state?
   - How to handle test isolation state?

2. **Restart Policy:**
   - How long to wait for resources?
   - Exponential backoff?
   - Max restart attempts?

3. **Container Tracking:**
   - Track via container ID registry?
   - Or via PGID (process group)?
   - How to handle docker-in-docker?

4. **Cross-Platform:**
   - Windows support for daemon?
   - macOS launchd integration?
   - FreeBSD jails?

5. **Multi-User:**
   - One daemon per user?
   - Or system-wide daemon?
   - How to handle permissions?

---

## Success Criteria

**Phase 1 (Daemon):**
- [ ] Daemon starts and runs as background process
- [ ] System resource monitoring works (CPU, memory)
- [ ] IPC server accepts connections
- [ ] Port tracking and cleanup works
- [ ] 33+ tests passing

**Phase 2 (Self-Protection):**
- [ ] Test runner monitors own resources
- [ ] 80% threshold triggers graceful shutdown
- [ ] Child processes killed
- [ ] Containers stopped
- [ ] Ports released
- [ ] Checkpoint saved
- [ ] 37+ tests passing

**Phase 3 (Restart):**
- [ ] Daemon detects resource recovery
- [ ] Runner automatically restarts
- [ ] Checkpoint restored correctly
- [ ] Tests resume from interruption point
- [ ] 30+ tests passing

**Production Readiness:**
- [ ] All existing 4,067 tests still pass
- [ ] Documentation complete
- [ ] systemd/launchd service files
- [ ] Zero regressions
- [ ] <1% performance overhead

---

## Timeline

**Week 1:** Daemon foundation (33+ tests)
**Week 2:** Self-protection (37+ tests)
**Week 3:** Automatic restart (30+ tests)

**Total:** 3 weeks, ~100 tests, 100% production-ready

---

## Conclusion

This design provides a **production-grade self-protecting test runner** with:

✅ **80% threshold enforcement** (self-monitoring)
✅ **Graceful shutdown** (cleanup children/containers/ports)
✅ **Automatic restart** (resume from checkpoint)
✅ **Shared daemon** (system-wide coordination)
✅ **Port management** (orphan detection and cleanup)
✅ **Cross-platform** (Linux full, macOS/Windows graceful degradation)

**Key Innovation:** Test runner that kills itself *before* system does, with clean recovery.

**Next Step:** Begin Phase 1 implementation (daemon foundation).

---

**End of Research & Design Document**
