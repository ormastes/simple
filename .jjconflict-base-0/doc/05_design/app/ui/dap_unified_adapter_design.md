# DAP Unified Adapter Design

**Date:** 2026-03-07
**Status:** Implemented
**Location:** `src/lib/nogc_sync_mut/dap/adapter/`

## 1. Overview

### Problem

The `DapServer` class previously maintained two separate fields for debug backends:

- `hook_context: InterpreterHookContext` -- for local interpreter debugging
- `remote_backend: Option<RemoteRiscV32Backend>` -- for remote/hardware debugging

Every handler method contained conditional branches to dispatch to the correct backend. Approximately 17 `if self.remote_backend.?:` / `else:` blocks were scattered across `server.spl` and `dap_handlers.spl`, duplicating logic for breakpoints, stepping, variable inspection, stack traces, and more. Adding a new backend (OpenOCD, Trace32, ST-Link) would have required touching every handler.

### Solution

Replace both fields with a single `adapter: DebugAdapter` field. The `DebugAdapter` trait defines a uniform interface of ~30 methods covering all debug operations. Each backend implements the trait once. The `DapServer` dispatches every request through `self.adapter.*()` with zero conditional branches on backend type.

### Result

- `DapServer` has one field (`adapter: DebugAdapter`) instead of two
- All ~17 conditional branches eliminated
- Handler code reads linearly -- no backend-specific forks
- Seven adapter implementations, from host interpreters to bare-metal probes
- New backends require only a trait implementation and a `DapServer.with_adapter()` call

## 2. Architecture

```
+------------------+         +------------------+
|   MCP Server     |         |   DAP Client     |
| (simple-mcp)     |         | (VS Code, etc.)  |
+--------+---------+         +--------+---------+
         |                            |
         |  MCP tool calls            |  DAP JSON messages
         v                            v
+--------------------------------------------------+
|                   DapServer                       |
|                                                   |
|  adapter: DebugAdapter  (single field)            |
|  breakpoint_manager: BreakpointManager            |
|  state: DebuggerState                             |
+------------------------+-------------------------+
                         |
                         | trait dispatch
                         v
+--------------------------------------------------+
|              trait DebugAdapter                    |
|  ~30 methods (connect, step, break, inspect, ...) |
|  capabilities() -> AdapterCapabilities            |
+--------------------------------------------------+
         |           |           |          |
    +----+----+ +----+----+ +---+----+ +---+-----+
    | Local   | | Remote  | | GdbMi  | | OpenOCD |
    | Adapter | | Adapter | | Adapter| | Adapter |
    +---------+ +---------+ +--------+ +---------+
         |           |           |          |
    +----+----+ +----+----+ +---+-----+
    | Trace32 | | T32Gdb  | | StLink  |
    | Adapter | | Adapter | | Tools   |
    +---------+ +---------+ | Adapter |
                             +---------+

Adapters wrap their respective clients:

  LocalAdapter       -> InterpreterHookContext  (host, software)
  RemoteAdapter      -> RemoteRiscV32Backend    (GDB stub, QEMU)
  GdbMiAdapter       -> GdbMiClient             (GDB/MI protocol)
  OpenocdAdapter     -> OpenocdClient           (OpenOCD + GDB)
  Trace32Adapter     -> Trace32Client           (Lauterbach API)
  T32GdbAdapter      -> T32GdbBridgeClient      (T32 GDB server + PRACTICE)
  StLinkToolsAdapter -> StLinkToolsClient       (st-flash / st-info CLI)
```

## 3. DebugAdapter Trait Method Reference

All methods are defined in `src/lib/nogc_sync_mut/dap/adapter/mod.spl`.

### Connection Management

| Method | Signature | Purpose |
|--------|-----------|---------|
| `name` | `fn name() -> text` | Adapter identifier (e.g. `"local-interpreter"`, `"gdb-mi"`) |
| `is_attached` | `fn is_attached() -> bool` | Whether the adapter is connected to a target |
| `attach` | `fn attach(program: text, args: [text]) -> Result<text, text>` | Connect to target, load symbols/program |
| `detach` | `fn detach() -> Result<text, text>` | Disconnect from target |

### Execution Control

| Method | Signature | Purpose |
|--------|-----------|---------|
| `halt` | `fn halt() -> Result<text, text>` | Async break -- pause running target |
| `resume` | `fn resume() -> Result<text, text>` | Continue execution |
| `single_step` | `fn single_step() -> Result<text, text>` | Step into (one instruction/statement) |
| `step_over` | `fn step_over() -> Result<text, text>` | Step over function calls |
| `step_out` | `fn step_out() -> Result<text, text>` | Run until current function returns |
| `reset` | `fn reset() -> Result<text, text>` | Restart execution from beginning |

### Breakpoints

| Method | Signature | Purpose |
|--------|-----------|---------|
| `set_breakpoint` | `fn set_breakpoint(file: text, line: i32) -> Result<i32, text>` | Set breakpoint at source location, returns BP id |
| `set_breakpoint_at_addr` | `fn set_breakpoint_at_addr(addr: i64) -> Result<i32, text>` | Set breakpoint at raw address (baremetal) |
| `delete_breakpoint` | `fn delete_breakpoint(id: i32) -> Result<text, text>` | Remove breakpoint by id |
| `set_watchpoint` | `fn set_watchpoint(expr: text, access: text) -> Result<i32, text>` | Set data breakpoint (read/write/readWrite) |
| `set_breakpoint_rich` | `fn set_breakpoint_rich(file, line, condition, hit_condition, log_message) -> Result<i32, text>` | Breakpoint with condition, hit count, and logpoint support |

### Variable Inspection

| Method | Signature | Purpose |
|--------|-----------|---------|
| `read_locals` | `fn read_locals() -> Result<[VarInfo], text>` | Local variables in current frame |
| `read_arguments` | `fn read_arguments() -> Result<[VarInfo], text>` | Function arguments in current frame |
| `read_globals` | `fn read_globals() -> Result<[VarInfo], text>` | Global/module-level variables |
| `evaluate` | `fn evaluate(expr: text) -> Result<text, text>` | Evaluate expression in current context |
| `list_children` | `fn list_children(var_ref: text) -> Result<[VarInfo], text>` | Expand struct/array children for nested variable display |

### Stack Inspection

| Method | Signature | Purpose |
|--------|-----------|---------|
| `stack_trace` | `fn stack_trace() -> Result<[FrameInfo], text>` | Full call stack |
| `stack_depth` | `fn stack_depth() -> Result<i32, text>` | Number of frames on the stack |
| `select_frame` | `fn select_frame(level: i32) -> Result<text, text>` | Set active frame for variable inspection |
| `current_location` | `fn current_location() -> Result<LocationInfo, text>` | File, line, and function name of current PC |

### Memory Access

| Method | Signature | Purpose |
|--------|-----------|---------|
| `read_memory` | `fn read_memory(addr: i64, size: i32) -> Result<[i32], text>` | Read raw bytes from target memory |
| `write_memory` | `fn write_memory(addr: i64, data: [i32]) -> Result<text, text>` | Write raw bytes to target memory |

### Register Access

| Method | Signature | Purpose |
|--------|-----------|---------|
| `read_register` | `fn read_register(name: text) -> Result<i64, text>` | Read single named register |
| `read_all_registers` | `fn read_all_registers() -> Result<Dict<text, i64>, text>` | Read all registers as name-value map |
| `write_register` | `fn write_register(name: text, value: i64) -> Result<text, text>` | Write a register value |

### Context Management

| Method | Signature | Purpose |
|--------|-----------|---------|
| `clear_context` | `fn clear_context() -> Result<text, text>` | Clear interpreter state for test isolation (no-op on hardware) |
| `reload_program` | `fn reload_program(program: text) -> Result<text, text>` | Reload/reflash program binary |
| `capabilities` | `fn capabilities() -> AdapterCapabilities` | Query what this adapter supports |

## 4. AdapterCapabilities

Defined in `src/lib/nogc_sync_mut/dap/adapter/mod.spl` as `class AdapterCapabilities`.

### Fields

| Field | Type | Meaning |
|-------|------|---------|
| `can_reset` | `bool` | Adapter can restart execution from the beginning |
| `can_reload` | `bool` | Adapter can reload/reflash a new program binary |
| `can_clear_context` | `bool` | Adapter can clear interpreter state (test isolation) |
| `supports_memory` | `bool` | `read_memory` / `write_memory` are functional |
| `supports_registers` | `bool` | Register read/write is functional |
| `supports_watchpoints` | `bool` | Hardware or software watchpoints are available |
| `supports_threads` | `bool` | Multi-thread debugging is available |
| `max_watchpoints` | `i32` | Maximum concurrent watchpoints (0 = none) |

### Capability Matrix by Adapter

| Adapter | reset | reload | clear_ctx | memory | registers | watchpoints | max_wp |
|---------|:-----:|:------:|:---------:|:------:|:---------:|:-----------:|:------:|
| **LocalAdapter** | Y | Y | Y | - | - | Y (sw) | 1024 |
| **RemoteAdapter** | Y | - | - | Y | Y | Y (hw) | hw-dependent |
| **GdbMiAdapter** | Y | - | - | Y | Y | - | 0 |
| **OpenocdAdapter** | Y | - | - | Y | Y | - | 0 |
| **Trace32Adapter** | Y | - | - | Y | Y | - | 0 |
| **T32GdbAdapter** | Y | - | - | Y | Y | - | 0 |
| **StLinkToolsAdapter** | Y | - | - | Y | - | - | 0 |

### Builder Pattern

`AdapterCapabilities` provides two static constructors and chainable builder methods:

```simple
# Start from nothing
AdapterCapabilities.basic()              # all false, max_watchpoints=0

# Start from everything
AdapterCapabilities.full()               # all true, max_watchpoints=1024

# Chain modifiers
AdapterCapabilities.basic()
    .with_reset()
    .with_memory()
    .with_registers()
    .with_watchpoints(4)
```

## 5. How to Add a New Debug Backend

Adding a new backend requires three steps. No changes to `DapServer`, `dap_handlers.spl`, or any existing adapter.

### Step 1: Create the adapter file

Create `src/lib/nogc_sync_mut/dap/adapter/my_backend.spl`:

```simple
use std.nogc_sync_mut.debug.coordinator.{VarInfo, FrameInfo, LocationInfo}
use std.nogc_sync_mut.dap.adapter.mod.{DebugAdapter, AdapterCapabilities, AdapterConfig}

class MyBackendAdapter:
    config: AdapterConfig
    attached: bool
    capabilities: AdapterCapabilities

impl MyBackendAdapter:
    static fn create(config: AdapterConfig) -> MyBackendAdapter:
        MyBackendAdapter(
            config: config,
            attached: false,
            capabilities: AdapterCapabilities.basic()
                .with_reset()
                .with_memory()
        )

    # Implement all DebugAdapter trait methods:
    fn name() -> text: "my-backend"
    fn is_attached() -> bool: self.attached
    fn attach(program: text, args: [text]) -> Result<text, text>: ...
    fn detach() -> Result<text, text>: ...
    # ... all ~30 methods
    fn capabilities() -> AdapterCapabilities: self.capabilities
```

### Step 2: Set capabilities honestly

Report only what the backend actually supports. Unsupported methods should return `Err("... not supported by my-backend")`. The `DapServer` uses `capabilities()` to decide what scopes to expose (e.g., the Registers scope is only shown when `supports_registers` is true).

### Step 3: Wire it up

```simple
val config = AdapterConfig(
    adapter_type: "my-backend",
    host: "192.168.1.100",
    port: 3333,
    program: "firmware.elf",
    args: [],
    timeout_ms: 30000,
    architecture: "riscv32"
)
val adapter = MyBackendAdapter.create(config)
val server = DapServer.with_adapter(adapter)
server.run()
```

Optionally add a static factory to `AdapterConfig` for convenience (e.g., `AdapterConfig.my_backend(...)`).

## 6. Host vs. Baremetal Differences

The `DebugAdapter` trait is the same for both environments. The difference is in which methods return `Ok` vs. `Err` and what `capabilities()` reports.

### Host (LocalAdapter)

- **Target:** Simple language interpreter running on the development machine
- **Memory/Registers:** Not applicable -- the interpreter operates on high-level values, not raw addresses. `read_memory`, `read_register`, etc. return `Err`.
- **Context management:** `clear_context()` resets the interpreter's variable tables for test isolation. `reload_program()` is planned but not yet implemented.
- **Watchpoints:** Software-based, implemented by polling variable values between steps. Capacity is effectively unlimited (`max_watchpoints: 1024`).
- **Breakpoints:** By source file and line only. Address-based breakpoints are not supported.

### Baremetal (RemoteAdapter, GdbMiAdapter, OpenocdAdapter, Trace32Adapter, T32GdbAdapter)

- **Target:** Physical MCU or QEMU emulator accessed via debug probe
- **Memory/Registers:** Fully supported -- read/write arbitrary addresses and CPU registers
- **Context management:** `clear_context()` is a no-op (hardware has no interpreter state to clear). `reload_program()` reflashes the ELF binary.
- **Watchpoints:** Hardware-based, limited by the CPU's debug unit (typically 2-4 on ARM Cortex-M, varies by architecture). `RemoteAdapter` queries the backend for the actual hardware capacity.
- **Breakpoints:** Both source-level and address-level. Hardware breakpoint count is limited by the debug unit.

### Flash-only (StLinkToolsAdapter)

- **Target:** STM32 MCU via ST-Link USB probe using `st-flash` / `st-info` CLI tools
- **Capabilities:** Flash programming, memory read, reset, chip identification only
- **Not supported:** Stepping, breakpoints, variables, stack traces, registers. All such methods return `Err` with a message suggesting OpenOCD+GDB as an alternative.

## 7. Relationship to DebugBackend Trait

There are two debug abstraction layers in the codebase:

| Trait | Location | Purpose | Method count |
|-------|----------|---------|:------------:|
| `DebugBackend` | `src/lib/nogc_sync_mut/debug/coordinator.spl` | Session-based coordinator routing | ~14 |
| `DebugAdapter` | `src/lib/nogc_sync_mut/dap/adapter/mod.spl` | DAP server direct dispatch | ~30 |

`DebugBackend` is the older, narrower trait used by `DebugCoordinator`. The coordinator routes commands by session ID to the correct backend (interpreter, SMF, native, or remote). It does not expose memory, register, or watchpoint operations.

`DebugAdapter` is the newer, richer trait used by `DapServer`. It covers all operations needed by the DAP protocol, including memory/register access, rich breakpoints, nested variable expansion, and capability reporting.

The two traits overlap substantially. `DebugBackend` has `run()` (not in `DebugAdapter`); `DebugAdapter` has memory, register, watchpoint, context management, and capability methods (not in `DebugBackend`). A future unification would merge them into a single trait, likely adopting `DebugAdapter`'s superset API and having the coordinator use it directly.

## 8. Known Semantic Mismatch: variables_reference==2

In `dap_handlers.spl`, the DAP `variables` request maps `variablesReference` values to scopes:

| Reference | DAP Scope Label | Actual data source |
|:---------:|-----------------|-------------------|
| 1 | "Local" | `adapter.read_locals()` |
| 2 | "Global" | `adapter.read_globals()` |
| 3 | "Registers" | `adapter.read_all_registers()` |

For **LocalAdapter**, reference 2 returns global/module-level variables via `InterpreterHookContext.variables_in_scope(0, VariableScope.Global)`.

For **RemoteAdapter**, `read_globals()` delegates to `gdb.read_globals()`, which in GDB/MI terms returns global symbols -- but the original code before the refactor used reference 2 to fetch *arguments* (`gdb.read_arguments()`), not globals.

This semantic mismatch is preserved intentionally. The displayed scope label is "Global" in both cases, so end users see consistent UI. However, remote users may see argument values where they expect globals. This is documented in the handler code:

```
# NOTE: ref=2 means "arguments" for remote, "globals" for local
# This semantic mismatch is preserved intentionally (see plan)
```

A future fix would split reference 2 into separate "Arguments" and "Globals" scopes, or have the adapter itself decide the mapping.
