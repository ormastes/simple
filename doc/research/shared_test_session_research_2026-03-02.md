# Shared Test Session Framework Research

**Date:** 2026-03-02
**Scope:** QEMU, baremetal, system test session sharing for faster test execution
**Languages surveyed:** Python, Ruby, TypeScript, Rust, Zig, Erlang/Elixir

---

## 1. Problem Statement

QEMU/baremetal tests are expensive: boot times range from 2-60 seconds per VM. Currently, each test or test file starts a fresh QEMU instance. For a suite of 100 baremetal tests, this means 100 boots. If boot takes 5 seconds, that's 500 seconds of pure overhead.

**Goal:** Share QEMU/connection sessions across non-destructive tests, while isolating destructive/crash tests.

---

## 2. Current Simple Infrastructure

### Existing Components

| Component | Location | Purpose |
|-----------|----------|---------|
| QemuConfig | `src/lib/nogc_async_mut_noalloc/qemu/mod.spl` | QEMU configuration (6 architectures) |
| QemuInstance | `qemu/mod.spl` | VM lifecycle (start/stop/wait) |
| QemuTestSession | `qemu/test_session.spl` | **Already has auto-reset between tests** |
| QemuMultiTestRunner | `qemu/test_session.spl` | Batch test execution with result collection |
| BootRunner | `qemu/boot_runner.spl` | High-level boot test API with serial capture |
| TestHarness | `baremetal/common/test_harness.spl` | In-guest test infrastructure |
| ExecutionConfig | `execution/mod.spl` | Three modes: Local, QEMU-GDB, x86_64-QEMU |
| SSpec | Built-in runtime | BDD framework with `describe`/`it`/`given`/`context_def` |

### Current Session Lifecycle

```
Per-test:  Boot QEMU -> Load binary -> Run test -> Kill QEMU
Per-group: Boot QEMU -> (auto-reset between tests) -> Kill QEMU  [QemuTestSession]
```

`QemuTestSession` already supports `with_auto_reset(true)` and `with_auto_reload(true)` for running multiple tests on one QEMU instance. This is the foundation to build on.

---

## 3. Cross-Language Survey

### 3.1 The Universal Three-Layer Pattern

Every mature framework converges on the same architecture:

```
Layer 1: EXPENSIVE RESOURCE (session/suite scope)
    Created once: QEMU VM, DB connection pool, browser process
    Torn down at end of entire run

Layer 2: GROUP RESET (module/context scope)
    Reset per test group: VM snapshot restore, DB transaction begin
    Provides clean starting point for related tests

Layer 3: PER-TEST ISOLATION (function/example scope)
    Rollback, savepoint, cookie clear, state reset
    Ensures each test sees predictable state
```

**Key insight:** Resource lifecycle and isolation lifecycle are decoupled. Keep the expensive resource alive (Layer 1) while providing isolation through a cheaper mechanism (Layer 3).

### 3.2 Framework Comparison

| Framework | Session Setup | Data Passing | Parallel Model | QEMU Approach |
|-----------|--------------|--------------|----------------|---------------|
| **pytest** | `scope="session"` fixture | Dependency injection via params | Multi-process (xdist) | One per test (Avocado-VT) |
| **RSpec** | `before(:suite)` / `let_it_be` | Instance variables / shared_context | Single-threaded | N/A |
| **Jest** | `globalSetup` | Filesystem only (cross-process) | Worker processes | N/A |
| **Vitest** | `globalSetup` + `provide` | `provide`/`inject` (serializable) | Worker threads | N/A |
| **Playwright** | Project dependencies | `storageState` files | Browser contexts | Best model for VMs |
| **Rust** | `LazyLock`/`OnceLock` | Static references | Threads (cargo test) | One QEMU per binary (phil-opp) |
| **Zig** | None built-in | File-scoped `var` | Single thread | One QEMU per run |
| **Erlang CT** | `init_per_suite/group` | Config proplist | Parallel groups | OTP supervisor |
| **Elixir** | `setup_all` / Ecto Sandbox | Allowance system | Async processes | Process-based |

### 3.3 Key Patterns Extracted

#### Pattern A: Layered Fixture Scopes (pytest)

```python
@pytest.fixture(scope="session")
def qemu_pool():
    pool = [boot_qemu(arch) for arch in ["x86_64", "arm64"]]
    yield pool
    for vm in pool: vm.shutdown()

@pytest.fixture(scope="module")
def qemu_session(qemu_pool):
    vm = qemu_pool.acquire()
    vm.snapshot_restore("golden")
    yield vm
    qemu_pool.release(vm)

@pytest.fixture(scope="function")
def clean_vm(qemu_session):
    qemu_session.snapshot_restore("module_start")
    yield qemu_session
```

#### Pattern B: Erlang Common Test Groups

```erlang
groups() -> [
    {boot_tests, [parallel], [test_boot_x86, test_boot_arm]},
    {uart_tests, [sequence],  [test_uart_init, test_uart_send]},
    {crash_tests, [],          [test_kernel_panic, test_watchdog]}
].

init_per_group(boot_tests, Config) ->
    VM = start_qemu(x86_64),
    [{vm, VM} | Config];
init_per_group(crash_tests, Config) ->
    %% Fresh VM per test - no sharing
    Config.

end_per_group(boot_tests, Config) ->
    stop_qemu(?config(vm, Config)).
```

**Key features:**
- Groups declare `[parallel]` or `[sequence]` execution
- `init_per_group`/`end_per_group` manage shared resources
- Config proplist passes state down through the group hierarchy
- Nested groups inherit parent group's config

#### Pattern C: Playwright Project Dependencies

```
Setup project (boots VM, saves state) -> Test projects (load saved state)
```

The long-lived process (browser/QEMU) stays running. Cheap, isolated sub-sessions are created within it. This maps directly to QEMU with snapshot/restore.

#### Pattern D: Ecto Sandbox Ownership (Elixir)

```elixir
# Test process checks out a connection (QEMU session)
checkout(session)
# Child processes are allowed to use the same session
allow(session, self(), child_pid)
# Connection is wrapped in a transaction (snapshot)
# On test end: rollback (restore snapshot)
```

**Modes:**
- **Manual:** Explicit checkout/allow (maximum isolation, more boilerplate)
- **Shared:** Any process can use the checked-out session (simpler, less isolation)

#### Pattern E: Test Tagging & Classification

```
read_only     -> Share VM, no reset between tests
mutating_safe -> Snapshot/restore between tests
destructive   -> Fresh VM per test (crash tests, etc.)
```

This is the cargo-nextest approach: scheduler-level resource control via test metadata.

---

## 4. QEMU-Specific Optimizations

### 4.1 Snapshot/Restore (Biggest Win)

| Operation | Time |
|-----------|------|
| Full QEMU boot | 2-60 seconds |
| `savevm`/`loadvm` | 1-2 seconds |
| Firecracker snapshot restore | ~100ms |
| Firecracker cold boot | ~125ms |
| QEMU microvm boot | 2-3 seconds |

**QMP commands for programmatic control:**
```json
{"execute": "savevm", "arguments": {"name": "golden"}}
{"execute": "loadvm", "arguments": {"name": "golden"}}
{"execute": "system_reset"}
{"execute": "query-status"}
```

### 4.2 qcow2 Overlay for Disk Isolation

```bash
# Create base image once
qemu-img create -f qcow2 base.qcow2 10G
# Per-test: thin overlay (copy-on-write, near-zero cost)
qemu-img create -f qcow2 -b base.qcow2 -F qcow2 test_overlay.qcow2
```

All disk writes go to overlay. Base image stays pristine. Overlay is discarded after test.

### 4.3 Communication Channels

| Channel | Latency | Use Case |
|---------|---------|----------|
| Serial (UART) | Low | Test output, simple commands |
| virtio-serial | Very low | Structured test data |
| QMP socket | Low | VM control (snapshots, reset) |
| ivshmem | Zero-copy | Large data transfer |
| GDB stub | Medium | Debugging, breakpoints |
| 9p filesystem | Medium | Shared file access |

### 4.4 NixOS Optimization Story

QEMU's 9p filesystem had O(n) linked-list lookup for file handles. Replacing with hash table reduced a 278k-file copy from **2 hours to 7 minutes** (17x). Lesson: profile the actual bottleneck.

---

## 5. Recommended Architecture for Simple

### 5.1 Session Broker Pattern

```
+----------------------------------------------------------+
|                    TestSessionBroker                      |
|                                                          |
|  fn acquire(arch, mode) -> SessionHandle                 |
|  fn release(handle)                                      |
|  fn health_check(handle) -> bool                         |
|                                                          |
|  Pool:                                                   |
|    x86_64:  [VM1(idle), VM2(in_use), VM3(idle)]         |
|    arm64:   [VM4(idle)]                                  |
|    riscv64: [VM5(idle)]                                  |
+----------------------------------------------------------+
```

### 5.2 Test Classification System

Tests declare their session requirements via metadata:

```simple
describe "UART basic read/write", session: :shared, mode: :read_only:
    # Shares VM with other read_only tests - no reset between tests
    it "reads from UART":
        val data = uart_read(session)
        expect(data).to_contain("Hello")

describe "Memory corruption test", session: :exclusive, mode: :destructive:
    # Gets a fresh VM - destroyed after
    it "corrupts kernel memory":
        write_to(0xDEAD_BEEF, 0xFF)
        # VM is expected to crash

describe "GPIO toggle", session: :shared, mode: :mutating:
    # Shares VM but gets snapshot/restore between tests
    it "sets pin high":
        gpio_set(13, HIGH)
        expect(gpio_read(13)).to_equal(HIGH)
```

### 5.3 Session Lifecycle with Snapshots

```
Suite Start:
    1. Boot QEMU instances into pool (1 per architecture needed)
    2. Each VM boots to "golden state" (OS loaded, test harness ready)
    3. savevm("golden") on each VM

Per Group (shared session):
    4. Acquire VM from pool
    5. loadvm("golden") or loadvm("group_start")
    6. Run init_per_group (e.g., load driver, configure peripheral)
    7. savevm("group_start")

Per Test (within group):
    read_only:    Run test, no reset
    mutating:     loadvm("group_start"), run test
    destructive:  N/A (never in shared group)

Group End:
    8. Release VM back to pool
    9. loadvm("golden") to reset for next group

Suite End:
    10. Shutdown all VMs in pool
```

### 5.4 SSpec Integration

Extend current SSpec with session-aware hooks:

```simple
# New hooks (additions to existing framework)
before_suite:
    # Boot QEMU pool - runs once per test run
    val pool = SessionBroker.start(architectures: ["x86_64", "riscv32"])
    set_suite_context(:pool, pool)

after_suite:
    get_suite_context(:pool).shutdown()

# Group-level session management
describe "Boot tests", qemu: :x86_64, session_mode: :shared:
    before_group:
        val session = get_suite_context(:pool).acquire(:x86_64)
        session.snapshot_restore("golden")
        set_group_context(:session, session)

    after_group:
        get_group_context(:session).release()

    it "reaches login prompt":
        val s = get_group_context(:session)
        expect(s.serial_output()).to_contain("login:")

    it "accepts root login":
        val s = get_group_context(:session)
        s.serial_send("root\n")
        expect(s.serial_output()).to_contain("#")
```

### 5.5 Parallel Execution Strategy

```
                    Test Scheduler
                         |
            +------------+------------+
            |            |            |
     [read_only]   [mutating]   [destructive]
     Worker Pool   Worker Pool  Sequential
     (shared VMs)  (snapshot    (fresh VM
      no reset)     restore)    per test)
```

**Sharding rules:**
- `read_only` tests grouped together, share one VM per architecture
- `mutating` tests each get snapshot/restore (costlier but isolated)
- `destructive` tests run sequentially, each gets a fresh VM
- Tests within a group run sequentially on their shared VM
- Groups across different architectures run in parallel

### 5.6 Crash Recovery

```simple
class SessionBroker:
    fn health_check(handle: SessionHandle) -> bool:
        # QMP query-status
        val status = handle.qmp_query("query-status")
        status.?running ?? false

    fn recover(handle: SessionHandle) -> Result<SessionHandle, text>:
        if not health_check(handle):
            # VM crashed - destroy and create new
            handle.force_kill()
            val new_vm = boot_qemu(handle.arch)
            new_vm.snapshot_restore("golden")
            Ok(new_vm)
        else:
            Ok(handle)
```

---

## 6. Expected Performance Impact

| Optimization | Current | With Sharing | Speedup |
|-------------|---------|-------------|---------|
| 100 read_only tests, 5s boot | 500s boot overhead | 5s (1 boot) | **100x** |
| 50 mutating tests, 5s boot, 1s restore | 250s boot | 50s restore | **5x** |
| 10 destructive tests | 50s (no change) | 50s | 1x |
| **Total (mixed 100/50/10)** | **800s** | **~105s** | **~7.6x** |

Additional optimizations stackable:
- QEMU microvm: 10-30x boot time reduction
- Parallel across architectures: Nx for N architectures
- Artifact caching: eliminates redundant binary builds

---

## 7. Implementation Priorities

### Phase 1: Session Broker + Test Tagging (Foundation)
- `SessionBroker` class with pool management
- Test metadata system: `session_mode: :read_only | :mutating | :destructive`
- QMP integration for snapshot/restore
- Extend `QemuTestSession` to use broker

### Phase 2: SSpec Integration
- `before_suite`/`after_suite` hooks
- `before_group`/`after_group` hooks
- Group-level context passing (`set_group_context`/`get_group_context`)
- Automatic session acquisition based on test metadata

### Phase 3: Parallel Execution
- Worker pool for parallel groups
- Sharding by session mode and architecture
- Load balancing across VM pool

### Phase 4: Advanced Optimizations
- qcow2 overlay support for disk isolation
- microvm configuration for sub-3s boot
- virtio-serial for structured test communication
- Artifact caching

---

## 8. Design Principles (from survey)

1. **Decouple resource lifecycle from isolation** - Keep expensive resource alive, isolate cheaply
2. **Declarative, not imperative** - Tests declare requirements via metadata, framework manages sessions
3. **Fail fast, recover gracefully** - Health checks detect dead VMs, broker replaces them
4. **Default to isolation** - New tests are `destructive` by default, opt-in to sharing
5. **Supervisor pattern** - Broker supervises VM pool like OTP supervisor supervises processes
6. **No magic sharing** - Tests explicitly declare sharing mode (like Ecto manual mode)

---

## Sources

### Python/Ruby
- [pytest fixture scopes](https://docs.pytest.org/en/stable/how-to/fixtures.html)
- [pytest-xdist shared fixtures](https://pytest-xdist.readthedocs.io/en/stable/how-to.html)
- [QEMU functional testing](https://www.qemu.org/docs/master/devel/testing/functional.html)
- [RSpec hooks](https://rspec.info/features/3-12/rspec-core/hooks/before-and-after-hooks/)
- [test-prof before_all](https://github.com/test-prof/test-prof)
- [Ecto SQL Sandbox](https://hexdocs.pm/ecto_sql/Ecto.Adapters.SQL.Sandbox.html)

### TypeScript/Rust/Zig
- [Vitest globalSetup](https://vitest.dev/config/globalsetup.html)
- [Playwright project dependencies](https://playwright.dev/docs/test-global-setup-teardown)
- [Rust session-scoped fixtures](https://vrajat.com/posts/rust-test-fixtures/)
- [Writing an OS in Rust - Testing](https://os.phil-opp.com/testing/)
- [cargo-nextest test groups](https://nexte.st/docs/configuration/test-groups/)

### Erlang/BEAM
- [Common Test Writing](https://www.erlang.org/doc/apps/common_test/write_test_chapter.html)
- [Common Test Groups](https://learnyousomeerlang.com/common-test-for-uncommon-tests)
- [PropEr stateful testing](https://proper-testing.github.io/apidocs/proper_statem.html)

### QEMU Optimizations
- [QEMU Snapshot API](https://airbus-seclab.github.io/qemu_blog/snapshot.html)
- [QMP Specification](https://www.qemu.org/docs/master/interop/qmp-spec.html)
- [QEMU microvm](https://www.qemu.org/docs/master/system/i386/microvm.html)
- [NixOS QEMU 17x speedup](https://determinate.systems/blog/qemu-fix/)
- [Firecracker snapshots](https://github.com/firecracker-microvm/firecracker)
- [CodeSandbox VM cloning](https://codesandbox.io/blog/how-we-clone-a-running-vm-in-2-seconds)
- [KUnit](https://docs.kernel.org/dev-tools/kunit/index.html)
- [LKFT at scale](https://lkft.linaro.org/tests/)
