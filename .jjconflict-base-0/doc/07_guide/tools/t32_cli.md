# T32 CLI — TRACE32 GUI-to-CLI Converter

Command-line interface that converts TRACE32 PowerView GUI operations into CLI commands. Enables scripted and interactive control of TRACE32 debug sessions without the GUI.

Full MCP tool parity: all 36 MCP tools have CLI mappings.

---

## Usage

```bash
simple t32 <command> [args...]
```

---

## Commands

### Session Management

```bash
simple t32 sessions                          # List all sessions
simple t32 sessions open <host> <port> <name> <arch>  # Open new session
simple t32 sessions close <id>               # Close session
simple t32 sessions use <id>                 # Switch active session
simple t32 sessions info <id>                # Show session details
```

### Core Selection (Multi-Core)

```bash
simple t32 cores                             # List cores in current session
simple t32 cores select <core_id>            # Switch active core
```

### Execution Commands

```bash
simple t32 cmd run <command> [--force]       # Run raw PRACTICE command
simple t32 cmm <script> [--wait] [--timeout=<ms>] [--capture-area] [--force]
simple t32 eval <expression>                 # Evaluate TRACE32 expression
```

### Window Operations

```bash
simple t32 windows                           # List all windows from catalogs
simple t32 window show <key>                 # Capture and show window content
simple t32 window open <key>                 # Open a window
simple t32 window describe <key>             # Show window actions and fields
simple t32 screenshot <window> [path]        # Save window screenshot
```

### Fields and Actions

```bash
simple t32 field get <key>                   # Get field value
simple t32 field set <key> <value>           # Set field value
simple t32 action list [window_key]          # List actions (optionally by window)
simple t32 action do <key> [args]            # Execute an action
```

### Observability

```bash
simple t32 status                            # Show CPU run state
simple t32 history [count]                   # Show command history (default 20)
simple t32 resources list                    # List MCP resources
simple t32 resource read <uri>               # Read resource by URI
simple t32 error-check                       # Check TRACE32 error state
```

### Headless / CMM Tools

```bash
simple t32 headless setup [--area=<name>] [--no-semihost] [--no-error-handler]
simple t32 area read [name] [--clear]        # Read AREA buffer
simple t32 cmm-commands [--group=G] [--search=S]  # Query PRACTICE command database
simple t32 cmm-validate <source> [--mode=<headless|interactive>]
```

### Job Management (Async)

```bash
simple t32 jobs list [--session=<id>]        # List async jobs
simple t32 jobs get <job_id>                 # Get job status
simple t32 jobs cancel <job_id>              # Cancel a running job
simple t32 jobs result <job_id>              # Get completed job result
```

### Dialog Control

```bash
simple t32 dialog parse <source>             # Parse CMM for dialog elements
simple t32 dialog get <label> [--type=<bool|string|value>]
simple t32 dialog set <label> [value] [--action=<set|select|deselect|disable|enable>]
simple t32 dialog click <label> [--capture-area] [--timeout=<ms>]
```

### Other

```bash
simple t32 shell                             # Start interactive REPL
simple t32 help                              # Show help
```

---

## Interactive Shell

`simple t32 shell` starts a REPL with a prompt showing the current session and core:

```
(none)> sessions open localhost 20000 stm32wb ARM
Session 'stm32wb' opened with id s1 at localhost:20000
s1> cores
s1> windows
s1> show register_view
s1:core0> do halt
s1:core0> status
s1:core0> cmd Break.Set main --force
s1:core0> eval Register.PP(PC)
s1:core0> jobs list
s1:core0> history
s1:core0> quit
```

Shell commands: `sessions`, `use`, `info`, `cores`, `core`, `windows`, `show`, `open`, `describe`, `set`, `do`, `cmd`, `cmm`, `eval`, `screenshot`, `status`, `history`, `resources`, `resource`, `headless`, `area`, `cmm-commands`, `cmm-validate`, `jobs`, `dialog`, `error-check`, `help`, `quit`.

---

## SDN Catalogs

Window definitions, actions, and fields are loaded from SDN catalog files at `config/t32/catalogs/`:

| File | Content |
|------|---------|
| `windows.sdn` | Window definitions (key, title, kind, open/capture commands) |
| `actions.sdn` | Action definitions (key, label, type, command template) |
| `fields.sdn` | Field definitions (key, label, value type, scope) |

### SDN Format

```sdn
window register_view
  title: CPU Registers
  kind: built_in
  capture_mode: print_parse
  open_command: Register.view /SpotLight
  capture_command: WinPrint.Register.view

action halt
  label: Halt Target
  type: execute
  command: Break

field symbol
  label: Symbol Name
  type: string
  scope: window
```

### Built-in Windows

| Key | Title | Open Command |
|-----|-------|-------------|
| `break_list` | Breakpoint List | `Break.List` |
| `register_view` | CPU Registers | `Register.view /SpotLight` |
| `var_local` | Local Variables | `Var.Local` |
| `var_watch` | Variable Watch | `Var.Watch` |
| `stack_frame` | Stack Frame | `Frame.view /Caller` |
| `memory_dump` | Memory Dump | `Data.dump` |
| `source_list` | Source Listing | `List.auto` |
| `trace_list` | Trace List | `Trace.List` |
| `coverage_list` | Code Coverage | `COVerage.ListFunc` |
| `task_list` | RTOS Tasks | `TASK.List` |
| `semihost_area` | Semihosting Output | `AREA` |

### Built-in Actions

| Key | Label | Command |
|-----|-------|---------|
| `go` | Resume Execution | `Go` |
| `halt` | Halt Target | `Break` |
| `step` | Single Step | `Step` |
| `step_over` | Step Over | `Step.Over` |
| `step_out` | Step Out | `Step.Out` |
| `set_break` | Set Breakpoint | `Break.Set {symbol}` |
| `clear_break` | Clear Breakpoint | `Break.Delete {symbol}` |
| `system_up` | System Up | `SYStem.Up` |
| `system_reset` | System Reset | `SYStem.ResetTarget` |
| `flash_program` | Flash Program | `FLASH.ReProgram ALL; ...` |
| `trace_init` | Initialize Trace | `Trace.Init; ...` |
| `coverage_reset` | Reset Coverage | `COVerage.Reset` |

---

## Architecture

```
simple t32 <cmd>
    |
    v
mod.spl (CLI dispatcher — 22 top-level commands)
    |-> bridge.spl        — shared execution layer (calls MCP functions directly)
    |-> render.spl        — output formatting (scalar, table, kv, list, gui_status)
    |-> commands.spl      — canonical 36-command registry (MCP tool mappings)
    |-> session.spl       — session registry (open/close/use/list)
    |-> core_context.spl  — core selection (multi-core SoCs)
    |-> window_model.spl  — window list/open/show/describe
    |-> catalog_loader.spl — SDN parser for windows/actions/fields
    |-> text_parser.spl   — output text formatting
    |-> cli_shell.spl     — interactive REPL (all verbs route through bridge)
    |-> types.spl         — shared types (T32Session, T32BridgeResult, etc.)
    |-> error_codes.spl   — error messages derived from commands registry
```

### MCP Parity

Every MCP tool (`t32_mcp/protocol.spl`) maps to a CLI command via `commands.spl`. The bridge layer (`bridge.spl`) calls MCP execution functions directly without JSON-RPC framing. Parity is enforced by `t32_cli_parity_guard_spec.spl`.

Communication with TRACE32 uses `t32rem` (Remote API CLI) under the hood. See [trace32_linux_setup.md](../backend/trace32_linux_setup.md) for host prerequisites.

---

## Source Code

- **CLI module:** `examples/10_tooling/trace32_tools/t32_cli/` (12 files)
- **MCP server:** `examples/10_tooling/trace32_tools/t32_mcp/` (12 files)
- **Catalogs:** `config/t32/catalogs/` (3 SDN files)
- **Tests:** `test/unit/app/t32_cli/` (14 spec files)
- **Host setup:** [backend/trace32_linux_setup.md](../backend/trace32_linux_setup.md)
