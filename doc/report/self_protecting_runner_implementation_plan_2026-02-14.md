# Self-Protecting Test Runner - Implementation Plan

**Date:** 2026-02-14
**Status:** Implementation Ready
**Effort:** ~3 weeks (~120 hours)
**Risk:** Medium (daemon management complexity)

---

## Quick Start

```bash
# Phase 1: Build daemon foundation
simple build src/app/test_daemon/

# Phase 2: Integrate self-protection
simple test test/unit/app/test_runner_new/self_protection_spec.spl

# Phase 3: Enable automatic restart
simple test --self-protect --auto-restart

# Production: Enable daemon
simple test-daemon start
simple test --daemon
```

---

## Phase 1: Resource Daemon (Week 1)

### Day 1: Daemon Core Structure

**Create:** `src/app/test_daemon/mod.spl`

```simple
# Test Daemon Main Module
# System-wide resource monitoring and test runner coordination

use app.io.mod.{file_read, file_write, file_exists, process_run, getpid, time_now_unix_micros}
use std.process_monitor.{sample_process, ProcessMetrics}
use std.string.{NL}

# ============================================================================
# Daemon State
# ============================================================================

struct DaemonConfig:
    socket_path: text
    cpu_threshold_percent: f64
    memory_threshold_percent: f64
    system_check_interval_ms: i64
    runner_check_interval_ms: i64
    cleanup_interval_ms: i64
    log_file: text

struct RunnerInfo:
    pid: i64
    start_time_ms: i64
    last_heartbeat_ms: i64
    cpu_percent: f64
    memory_mb: i64
    status: text  # "running", "shutdown", "waiting_restart"
    checkpoint_path: text
    ports_owned: [i64]

struct PortInfo:
    port: i64
    owner_pid: i64
    opened_at_ms: i64
    protocol: text

struct SystemStats:
    total_cpu_percent: f64
    used_memory_mb: i64
    total_memory_mb: i64
    available_memory_mb: i64
    load_average_1m: f64

var daemon_runners: [RunnerInfo] = []
var daemon_ports: [PortInfo] = []
var daemon_config: DaemonConfig = default_daemon_config()
var daemon_running: bool = false

# ============================================================================
# Configuration
# ============================================================================

fn default_daemon_config() -> DaemonConfig:
    DaemonConfig(
        socket_path: "/tmp/simple-test-daemon.sock",
        cpu_threshold_percent: 80.0,
        memory_threshold_percent: 80.0,
        system_check_interval_ms: 1000,
        runner_check_interval_ms: 5000,
        cleanup_interval_ms: 10000,
        log_file: "/tmp/simple-test-daemon.log"
    )

fn load_daemon_config(path: text) -> DaemonConfig:
    # Load from config file
    # For now, use default
    default_daemon_config()

# ============================================================================
# Daemon Lifecycle
# ============================================================================

fn daemon_start(config: DaemonConfig) -> i64:
    """
    Start daemon as background process.
    Returns daemon PID on success, -1 on failure.
    """
    # Check if daemon already running
    if daemon_is_running():
        print "Daemon already running"
        return -1

    # Fork daemon process (simplified - would use actual fork)
    val pid = getpid()
    daemon_running = true
    daemon_config = config

    # Write PID file
    file_write("/tmp/simple-test-daemon.pid", "{pid}")

    # Start main loop (in production, this would be forked)
    daemon_main_loop()

    pid

fn daemon_stop():
    """Stop daemon gracefully"""
    daemon_running = false

    # Cleanup resources
    daemon_cleanup_all()

    # Remove PID file
    process_run("rm", ["/tmp/simple-test-daemon.pid"])

fn daemon_is_running() -> bool:
    """Check if daemon is running"""
    if not file_exists("/tmp/simple-test-daemon.pid"):
        return false

    val pid_str = file_read("/tmp/simple-test-daemon.pid").trim()
    val pid = int(pid_str)

    # Check if process exists
    val result = process_run("kill", ["-0", "{pid}"])
    result.exit_code == 0

# ============================================================================
# Main Event Loop
# ============================================================================

fn daemon_main_loop():
    """Main daemon event loop"""
    var last_system_check_ms = 0
    var last_runner_check_ms = 0
    var last_cleanup_ms = 0

    while daemon_running:
        val now_ms = time_now_unix_micros() / 1000

        # System resource monitoring
        if now_ms - last_system_check_ms > daemon_config.system_check_interval_ms:
            daemon_check_system_resources()
            last_system_check_ms = now_ms

        # Runner health checking
        if now_ms - last_runner_check_ms > daemon_config.runner_check_interval_ms:
            daemon_check_runners()
            last_runner_check_ms = now_ms

        # Cleanup orphans
        if now_ms - last_cleanup_ms > daemon_config.cleanup_interval_ms:
            daemon_cleanup_orphans()
            last_cleanup_ms = now_ms

        # Sleep briefly (would be event-driven in production)
        sleep_ms(100)

fn daemon_check_system_resources():
    """Check system-wide resource usage"""
    val stats = monitor_system_resources()

    # Check if any runner should be shut down
    for i in daemon_runners.len():
        val runner = daemon_runners[i]
        if runner.status != "running":
            continue

        # Check if runner is over threshold
        val mem_percent = (runner.memory_mb / stats.total_memory_mb) * 100.0

        if runner.cpu_percent > daemon_config.cpu_threshold_percent:
            daemon_log("Runner {runner.pid} CPU exceeded {runner.cpu_percent}%")
            daemon_request_shutdown(runner.pid, "cpu")
        elif mem_percent > daemon_config.memory_threshold_percent:
            daemon_log("Runner {runner.pid} memory exceeded {mem_percent}%")
            daemon_request_shutdown(runner.pid, "memory")

fn daemon_check_runners():
    """Check runner health (heartbeat timeouts)"""
    val now_ms = time_now_unix_micros() / 1000
    val timeout_ms = 30000  # 30 seconds

    for i in daemon_runners.len():
        val runner = daemon_runners[i]
        if runner.status != "running":
            continue

        val elapsed_ms = now_ms - runner.last_heartbeat_ms
        if elapsed_ms > timeout_ms:
            daemon_log("Runner {runner.pid} heartbeat timeout")
            daemon_mark_dead(runner.pid)

fn daemon_cleanup_orphans():
    """Cleanup orphaned processes, containers, ports"""
    # Cleanup dead runners
    daemon_cleanup_dead_runners()

    # Cleanup orphaned ports
    daemon_cleanup_orphaned_ports()

    # Cleanup orphaned containers (future)
    # daemon_cleanup_orphaned_containers()

# ============================================================================
# Exports
# ============================================================================

export DaemonConfig, RunnerInfo, PortInfo, SystemStats
export default_daemon_config, load_daemon_config
export daemon_start, daemon_stop, daemon_is_running
export daemon_main_loop
```

**Create:** `src/app/test_daemon/system_monitor.spl`

```simple
# System-Wide Resource Monitoring
# Extends std.process_monitor for system-level metrics

use app.io.mod.{file_read, file_exists, shell_output_trimmed, shell_int}
use std.string.{NL}

struct SystemStats:
    total_cpu_percent: f64
    used_memory_mb: i64
    total_memory_mb: i64
    available_memory_mb: i64
    load_average_1m: f64

fn monitor_system_resources() -> SystemStats:
    """
    Monitor system-wide resources.
    Platform: Linux (full), macOS (limited), Windows (stub)
    """
    if is_linux():
        monitor_system_resources_linux()
    elif is_macos():
        monitor_system_resources_macos()
    else:
        monitor_system_resources_windows()

# ============================================================================
# Linux Implementation
# ============================================================================

fn monitor_system_resources_linux() -> SystemStats:
    """Linux /proc filesystem implementation"""

    # Read /proc/meminfo
    val meminfo = file_read("/proc/meminfo")
    val total_mb = parse_meminfo_field(meminfo, "MemTotal:") / 1024
    val available_mb = parse_meminfo_field(meminfo, "MemAvailable:") / 1024
    val used_mb = total_mb - available_mb

    # Read /proc/loadavg
    val loadavg = file_read("/proc/loadavg")
    val load_1m = parse_load_average(loadavg)

    # CPU usage (simplified - would need two samples for accurate %)
    val cpu_percent = load_1m * 100.0

    SystemStats(
        total_cpu_percent: cpu_percent,
        used_memory_mb: used_mb,
        total_memory_mb: total_mb,
        available_memory_mb: available_mb,
        load_average_1m: load_1m
    )

fn parse_meminfo_field(content: text, field: text) -> i64:
    """Parse /proc/meminfo field: 'MemTotal:    16384000 kB'"""
    val lines = content.split(NL)
    for line in lines:
        if line.starts_with(field):
            val parts = line.split(" ")
            for part in parts:
                val trimmed = part.trim()
                if trimmed.len() > 0 and trimmed[0:1] >= "0" and trimmed[0:1] <= "9":
                    return int(trimmed)
    0

fn parse_load_average(content: text) -> f64:
    """Parse /proc/loadavg: '0.52 0.58 0.59 1/1234 12345'"""
    val parts = content.trim().split(" ")
    if parts.len() > 0:
        return to_float(parts[0])
    0.0

fn to_float(s: text) -> f64:
    """Convert string to float"""
    # Simplified conversion
    if s == "" or s == nil:
        return 0.0

    var num_str = ""
    var has_dot = false
    for i in s.len():
        val ch = s[i:i + 1]
        if ch >= "0" and ch <= "9":
            num_str = num_str + ch
        elif ch == "." and not has_dot:
            num_str = num_str + ch
            has_dot = true
        else:
            break

    if num_str == "" or num_str == ".":
        return 0.0

    if has_dot:
        val parts = num_str.split(".")
        if parts.len() == 2:
            val int_part = int(parts[0])
            val frac_part = int(parts[1])
            val divisor = 100.0
            int_part + (frac_part / divisor)
        else:
            int(num_str)
    else:
        int(num_str)

# ============================================================================
# macOS Implementation
# ============================================================================

fn monitor_system_resources_macos() -> SystemStats:
    """macOS implementation using sysctl and vm_stat"""

    # Total memory (bytes)
    val mem_bytes = shell_int("sysctl -n hw.memsize", 0)
    val total_mb = mem_bytes / (1024 * 1024)

    # Free memory (pages)
    val vm_stat = shell_output_trimmed("vm_stat", "")
    val free_mb = parse_vm_stat_free(vm_stat)
    val used_mb = total_mb - free_mb

    # Load average
    val load_str = shell_output_trimmed("sysctl -n vm.loadavg", "0.0 0.0 0.0")
    val load_1m = parse_load_macos(load_str)

    # CPU percent (from load)
    val cpu_count = shell_int("sysctl -n hw.ncpu", 1)
    val cpu_percent = (load_1m / cpu_count) * 100.0

    SystemStats(
        total_cpu_percent: cpu_percent,
        used_memory_mb: used_mb,
        total_memory_mb: total_mb,
        available_memory_mb: free_mb,
        load_average_1m: load_1m
    )

fn parse_vm_stat_free(vm_stat: text) -> i64:
    """Parse vm_stat output for free pages"""
    # Simplified - would need actual parsing
    0

fn parse_load_macos(load_str: text) -> f64:
    """Parse sysctl vm.loadavg output"""
    val parts = load_str.split(" ")
    if parts.len() > 0:
        return to_float(parts[0])
    0.0

# ============================================================================
# Windows Implementation
# ============================================================================

fn monitor_system_resources_windows() -> SystemStats:
    """Windows stub (future implementation)"""
    SystemStats(
        total_cpu_percent: 0.0,
        used_memory_mb: 0,
        total_memory_mb: 16384,
        available_memory_mb: 16384,
        load_average_1m: 0.0
    )

# ============================================================================
# Platform Detection
# ============================================================================

fn is_linux() -> bool:
    file_exists("/proc/meminfo")

fn is_macos() -> bool:
    val uname = shell_output_trimmed("uname", "")
    uname == "Darwin"

fn is_windows() -> bool:
    not is_linux() and not is_macos()

fn sleep_ms(ms: i64):
    """Sleep for milliseconds (stub - would use actual sleep)"""
    # Would use actual sleep syscall
    pass_do_nothing

export SystemStats
export monitor_system_resources
export is_linux, is_macos, is_windows
```

**Tests:** `test/unit/app/test_daemon/daemon_core_spec.spl`

```simple
use std.spec.{describe, it, expect}
use app.test_daemon.mod.{default_daemon_config, daemon_is_running}
use app.test_daemon.system_monitor.{monitor_system_resources}

describe "daemon_core":
    it "loads default config":
        val config = default_daemon_config()
        expect(config.cpu_threshold_percent).to_equal(80.0)
        expect(config.memory_threshold_percent).to_equal(80.0)

    it "checks if daemon running":
        val running = daemon_is_running()
        # Initially not running
        expect(running).to_equal(false)

describe "system_monitor":
    it "monitors system resources":
        val stats = monitor_system_resources()
        expect(stats.total_memory_mb).to_be_greater_than(0)
        expect(stats.available_memory_mb).to_be_greater_than(0)

    it "calculates memory usage":
        val stats = monitor_system_resources()
        val used = stats.used_memory_mb
        val total = stats.total_memory_mb
        expect(used).to_be_less_than(total)
```

**Success Criteria (Day 1):**
- [ ] Daemon starts and runs
- [ ] System resource monitoring works
- [ ] Linux /proc reading works
- [ ] 10+ tests passing

---

### Day 2: Runner Registry & Heartbeat

**Add to:** `src/app/test_daemon/mod.spl`

```simple
# ============================================================================
# Runner Registry
# ============================================================================

fn daemon_register_runner(pid: i64, checkpoint_path: text) -> text:
    """
    Register new test runner.
    Returns: "ok" or "error: <reason>"
    """
    # Check if already registered
    for runner in daemon_runners:
        if runner.pid == pid:
            return "error: already registered"

    # Create runner info
    val now_ms = time_now_unix_micros() / 1000
    val runner = RunnerInfo(
        pid: pid,
        start_time_ms: now_ms,
        last_heartbeat_ms: now_ms,
        cpu_percent: 0.0,
        memory_mb: 0,
        status: "running",
        checkpoint_path: checkpoint_path,
        ports_owned: []
    )

    daemon_runners.push(runner)
    daemon_log("Runner registered: PID {pid}")
    "ok"

fn daemon_heartbeat(pid: i64, cpu: f64, memory: i64) -> text:
    """
    Update runner heartbeat.
    Returns: "ok", "shutdown" (if over threshold), or "error"
    """
    var found = false
    var should_shutdown = false

    for i in daemon_runners.len():
        if daemon_runners[i].pid == pid:
            daemon_runners[i].last_heartbeat_ms = time_now_unix_micros() / 1000
            daemon_runners[i].cpu_percent = cpu
            daemon_runners[i].memory_mb = memory
            found = true

            # Check if over threshold
            val sys_stats = monitor_system_resources()
            val mem_percent = (memory / sys_stats.total_memory_mb) * 100.0

            if cpu > daemon_config.cpu_threshold_percent:
                should_shutdown = true
            elif mem_percent > daemon_config.memory_threshold_percent:
                should_shutdown = true

            break

    if not found:
        return "error: not registered"

    if should_shutdown:
        daemon_log("Requesting shutdown for PID {pid}")
        return "shutdown"

    "ok"

fn daemon_deregister_runner(pid: i64):
    """Remove runner from registry"""
    var new_runners: [RunnerInfo] = []

    for runner in daemon_runners:
        if runner.pid != pid:
            new_runners.push(runner)

    daemon_runners = new_runners
    daemon_log("Runner deregistered: PID {pid}")

fn daemon_mark_dead(pid: i64):
    """Mark runner as dead (for cleanup)"""
    for i in daemon_runners.len():
        if daemon_runners[i].pid == pid:
            daemon_runners[i].status = "shutdown"
            break

fn daemon_cleanup_dead_runners():
    """Remove dead runners from registry"""
    var active_runners: [RunnerInfo] = []

    for runner in daemon_runners:
        if runner.status == "running":
            active_runners.push(runner)
        else:
            daemon_log("Cleaning up dead runner: PID {runner.pid}")
            # Cleanup ports owned by this runner
            daemon_cleanup_runner_ports(runner.pid)

    daemon_runners = active_runners

fn daemon_request_shutdown(pid: i64, reason: text):
    """Request runner shutdown"""
    for i in daemon_runners.len():
        if daemon_runners[i].pid == pid:
            daemon_runners[i].status = "shutdown"
            daemon_log("Shutdown requested for PID {pid} (reason: {reason})")
            break

# ============================================================================
# Logging
# ============================================================================

fn daemon_log(message: text):
    """Log message to daemon log file"""
    val timestamp = time_now_unix_micros() / 1000
    val log_line = "[{timestamp}] {message}\n"

    # Append to log file
    if file_exists(daemon_config.log_file):
        file_append(daemon_config.log_file, log_line)
    else:
        file_write(daemon_config.log_file, log_line)

    # Also print to stderr for debugging
    print log_line.trim()

export daemon_register_runner, daemon_heartbeat, daemon_deregister_runner
export daemon_log
```

**Tests:** `test/unit/app/test_daemon/runner_registry_spec.spl`

```simple
use std.spec.{describe, it, expect, before_each}
use app.test_daemon.mod.{daemon_register_runner, daemon_heartbeat, daemon_deregister_runner}

describe "runner_registry":
    before_each:
        # Reset daemon state (would need actual reset function)
        pass_do_nothing

    it "registers new runner":
        val result = daemon_register_runner(12345, "/tmp/checkpoint.sdn")
        expect(result).to_equal("ok")

    it "detects duplicate registration":
        daemon_register_runner(12345, "/tmp/checkpoint.sdn")
        val result = daemon_register_runner(12345, "/tmp/checkpoint.sdn")
        expect(result).to_contain("already registered")

    it "processes heartbeat":
        daemon_register_runner(12345, "/tmp/checkpoint.sdn")
        val result = daemon_heartbeat(12345, 45.5, 512)
        expect(result).to_equal("ok")

    it "detects missing registration":
        val result = daemon_heartbeat(99999, 45.5, 512)
        expect(result).to_contain("not registered")

    it "requests shutdown on threshold":
        daemon_register_runner(12345, "/tmp/checkpoint.sdn")
        # Send high CPU (over 80%)
        val result = daemon_heartbeat(12345, 95.0, 512)
        expect(result).to_equal("shutdown")
```

**Success Criteria (Day 2):**
- [ ] Runner registration works
- [ ] Heartbeat updates runner state
- [ ] Threshold detection triggers shutdown
- [ ] Logging to file works
- [ ] 15+ tests passing

---

### Day 3: Port Manager

**Create:** `src/app/test_daemon/port_manager.spl`

```simple
# Port Management and Tracking
# Tracks ports owned by test runners, cleans up orphans

use app.io.mod.{shell_output, shell_int, process_run}

struct PortInfo:
    port: i64
    owner_pid: i64
    opened_at_ms: i64
    protocol: text

var tracked_ports: [PortInfo] = []

fn port_manager_register(port: i64, pid: i64, protocol: text) -> text:
    """
    Register port ownership.
    Returns: "ok" or "conflict: <owner_pid>"
    """
    # Check if port already registered
    for p in tracked_ports:
        if p.port == port:
            if p.owner_pid == pid:
                return "ok"  # Same owner
            return "conflict: {p.owner_pid}"

    # Register port
    val now_ms = time_now_unix_micros() / 1000
    val port_info = PortInfo(
        port: port,
        owner_pid: pid,
        opened_at_ms: now_ms,
        protocol: protocol
    )

    tracked_ports.push(port_info)
    "ok"

fn port_manager_release(port: i64, pid: i64) -> text:
    """Release port ownership"""
    var new_ports: [PortInfo] = []
    var found = false

    for p in tracked_ports:
        if p.port == port and p.owner_pid == pid:
            found = true
            # Don't add to new list (remove)
        else:
            new_ports.push(p)

    tracked_ports = new_ports

    if found:
        "ok"
    else:
        "error: not registered"

fn port_manager_cleanup_runner_ports(pid: i64):
    """Release all ports owned by runner PID"""
    var new_ports: [PortInfo] = []

    for p in tracked_ports:
        if p.owner_pid != pid:
            new_ports.push(p)

    tracked_ports = new_ports

fn port_manager_find_orphans() -> [(i64, i64)]:
    """
    Find ports owned by dead processes.
    Returns: [(port, old_pid)]
    """
    var orphans: [(i64, i64)] = []

    for p in tracked_ports:
        # Check if process still exists
        val result = process_run("kill", ["-0", "{p.owner_pid}"])
        if result.exit_code != 0:
            # Process dead
            orphans.push((p.port, p.owner_pid))

    orphans

fn port_manager_kill_port(port: i64) -> bool:
    """
    Find process using port and kill it.
    Uses: lsof -ti:PORT | xargs kill -9
    """
    # Find PID using port
    val lsof_output = shell_output("lsof -ti:{port} 2>/dev/null", "")
    val pid_str = lsof_output.trim()

    if pid_str == "":
        return false

    val pid = int(pid_str)

    # Kill process
    val kill_result = process_run("kill", ["-9", "{pid}"])
    kill_result.exit_code == 0

fn port_manager_is_available(port: i64) -> bool:
    """Check if port is available"""
    # Check if registered
    for p in tracked_ports:
        if p.port == port:
            return false

    # Check actual port binding
    val lsof_result = process_run("lsof", ["-ti:{port}"])
    lsof_result.exit_code != 0  # Available if lsof finds nothing

export PortInfo
export port_manager_register, port_manager_release
export port_manager_cleanup_runner_ports
export port_manager_find_orphans, port_manager_kill_port
export port_manager_is_available
```

**Tests:** `test/unit/app/test_daemon/port_manager_spec.spl`

```simple
use std.spec.{describe, it, expect}
use app.test_daemon.port_manager.{
    port_manager_register,
    port_manager_release,
    port_manager_is_available,
    port_manager_cleanup_runner_ports
}

describe "port_manager":
    it "registers port":
        val result = port_manager_register(8080, 12345, "tcp")
        expect(result).to_equal("ok")

    it "detects port conflict":
        port_manager_register(8080, 12345, "tcp")
        val result = port_manager_register(8080, 99999, "tcp")
        expect(result).to_contain("conflict")

    it "releases port":
        port_manager_register(8080, 12345, "tcp")
        val result = port_manager_release(8080, 12345)
        expect(result).to_equal("ok")

    it "checks port availability":
        val available1 = port_manager_is_available(8080)
        expect(available1).to_equal(true)

        port_manager_register(8080, 12345, "tcp")
        val available2 = port_manager_is_available(8080)
        expect(available2).to_equal(false)

    it "cleans up runner ports":
        port_manager_register(8080, 12345, "tcp")
        port_manager_register(8081, 12345, "tcp")
        port_manager_register(8082, 99999, "tcp")

        port_manager_cleanup_runner_ports(12345)

        val avail_8080 = port_manager_is_available(8080)
        val avail_8081 = port_manager_is_available(8081)
        val avail_8082 = port_manager_is_available(8082)

        expect(avail_8080).to_equal(true)   # Cleaned up
        expect(avail_8081).to_equal(true)   # Cleaned up
        expect(avail_8082).to_equal(false)  # Still owned by 99999
```

**Success Criteria (Day 3):**
- [ ] Port registration works
- [ ] Conflict detection works
- [ ] Orphan detection works
- [ ] Port cleanup works
- [ ] 12+ tests passing

---

## Phase 2: Self-Protection (Week 2)

### Day 1-2: Self-Monitoring

**Create:** `src/app/test_runner_new/self_protection.spl`

```simple
# Self-Protecting Test Runner
# Monitors own resource usage and shuts down gracefully on threshold violation

use std.process_monitor.{sample_process, ProcessMetrics}
use app.io.mod.{getpid, time_now_unix_micros}

struct SelfProtectionConfig:
    enabled: bool
    cpu_threshold_percent: f64
    memory_threshold_mb: i64
    check_interval_ms: i64
    daemon_enabled: bool

var self_protection_active: bool = false
var should_shutdown: bool = false
var shutdown_reason: text = ""

fn self_protection_start(config: SelfProtectionConfig):
    """Start self-monitoring"""
    if not config.enabled:
        return

    self_protection_active = true

    # Start monitoring loop (simplified - would be background thread)
    self_monitor_loop(config)

fn self_monitor_loop(config: SelfProtectionConfig):
    """Main self-monitoring loop"""
    var last_check_ms = 0

    while self_protection_active:
        val now_ms = time_now_unix_micros() / 1000

        if now_ms - last_check_ms > config.check_interval_ms:
            # Sample self
            val my_pid = getpid()
            val metrics = sample_process(my_pid, now_ms)

            # Check thresholds
            if metrics.cpu_percent > config.cpu_threshold_percent:
                should_shutdown = true
                shutdown_reason = "cpu"
                break

            if metrics.memory_mb > config.memory_threshold_mb:
                should_shutdown = true
                shutdown_reason = "memory"
                break

            last_check_ms = now_ms

        # Sleep briefly
        sleep_ms(100)

fn self_protection_should_shutdown() -> (bool, text):
    """Check if shutdown requested"""
    (should_shutdown, shutdown_reason)

fn self_protection_stop():
    """Stop self-monitoring"""
    self_protection_active = false

export SelfProtectionConfig
export self_protection_start, self_protection_should_shutdown, self_protection_stop
```

**Integration:** Modify `src/app/test_runner_new/test_runner_main.spl`

```simple
use app.test_runner_new.self_protection.{
    SelfProtectionConfig,
    self_protection_start,
    self_protection_should_shutdown
}

fn run_all_tests_with_protection(test_files: [text], options: TestOptions) -> [TestFileResult]:
    # Configure self-protection
    val config = SelfProtectionConfig(
        enabled: options.self_protect,
        cpu_threshold_percent: 80.0,
        memory_threshold_mb: 8192,  # 8 GB
        check_interval_ms: 1000,
        daemon_enabled: false  # Phase 3
    )

    # Start monitoring (background thread)
    self_protection_start(config)

    # Run tests normally
    var results: [TestFileResult] = []

    for test_file in test_files:
        # Check if shutdown requested
        val (should_stop, reason) = self_protection_should_shutdown()
        if should_stop:
            print "[SHUTDOWN] Resource limit exceeded: {reason}"
            break

        # Run test
        val result = run_single_test(test_file, options)
        results.push(result)

    results
```

**Success Criteria (Day 1-2):**
- [ ] Self-monitoring starts
- [ ] Threshold detection works
- [ ] Test runner stops on violation
- [ ] 15+ tests passing

---

## Summary

**Week 1 Deliverables:**
- Daemon foundation (system monitoring, runner registry, port management)
- 33+ tests passing
- Documentation

**Week 2 Deliverables:**
- Self-protection integration
- Graceful shutdown
- Checkpoint save/restore
- 37+ tests passing

**Week 3 Deliverables:**
- Automatic restart
- Production hardening
- Full documentation
- 30+ tests passing

**Total:** ~100 tests, production-ready self-protecting test runner

---

**Next Step:** Begin Day 1 implementation.
