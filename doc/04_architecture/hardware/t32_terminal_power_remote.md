# Architecture: T32 Terminal, Power Control & Remote Test Runner

**Date:** 2026-03-29
**Status:** Draft
**Requirements:** `doc/02_requirements/feature/t32_terminal_power_remote.md`

---

## 1. Module Layout

All new modules reside under `src/lib/nogc_sync_mut/terminal/` (sync, mutable, no GC -- matches network I/O classification).

```
src/lib/nogc_sync_mut/terminal/
  __init__.spl                          # Module init, re-exports
  types.spl                             # Terminal + power type definitions
  connection.spl                        # Terminal dispatch layer
  ssh_terminal.spl                      # SSH terminal implementation
  telnet_terminal.spl                   # Telnet terminal implementation
  t32_swd_terminal.spl                  # T32 SWD serial terminal
  relay_terminal.spl                    # Relay script terminal
  credential/
    store.spl                           # Encrypt/decrypt/resolve credentials
    config_parser.spl                   # SDN config -> typed structs
  power/
    __init__.spl                        # Power module init
    controller.spl                      # Power dispatch layer
    t32_power.spl                       # T32 SYStem power control
    relay_power.spl                     # Relay .shs script power
    host_power.spl                      # Host PC WoL/SSH power

src/lib/nogc_sync_mut/net/
  telnet.spl                            # Telnet protocol client (RFC 854)

src/lib/nogc_async_mut/mcp/
  main_lazy_terminal_tools.spl          # 8 terminal MCP tool handlers
  main_lazy_power_tools.spl             # 6 power MCP tool handlers
  main_lazy_remote_test_tools.spl       # 3 remote test MCP tool handlers

src/app/test_daemon/adapters/
  remote_pc_adapter.spl                 # Remote PC session adapter (kind 9)

config/t32/
  t32_terminal.sdn                      # Terminal + power SDN config
```

---

## 2. Dispatch Pattern

The project forbids inheritance. All polymorphism uses **kind-based dispatch** with integer constants and explicit `match` statements.

### 2.1 Terminal Dispatch

```
terminal_connect(config: TerminalConfig) -> Result<TerminalConnection, text>
  match config.kind:
    TERM_KIND_SSH (0)     -> ssh_terminal_connect(config)
    TERM_KIND_TELNET (1)  -> telnet_terminal_connect(config)
    TERM_KIND_T32_SWD (2) -> t32_swd_terminal_connect(config)
    TERM_KIND_RELAY (3)   -> relay_terminal_connect(config)
    _                     -> Err("unknown terminal kind")
```

Same pattern for `terminal_send`, `terminal_receive`, `terminal_execute`, `terminal_close`.

### 2.2 Power Dispatch

```
power_on(config: PowerConfig) -> Result<text, text>
  match config.kind:
    POWER_KIND_T32 (0)   -> t32_power_on(config)
    POWER_KIND_RELAY (1) -> relay_power_on(config)
    POWER_KIND_HOST (2)  -> host_power_on(config)
    _                    -> Err("unknown power kind")
```

Same pattern for `power_off`, `power_toggle`, `power_reset`, `power_state`.

---

## 3. Config Flow

```
  SDN file (config/t32/t32_terminal.sdn)
         |
         v
  SDN parser (existing std.sdn module)
         |
         v
  config_parser.spl
  - parse_terminal_configs() -> List<TerminalConfig>
  - parse_power_configs() -> List<PowerConfig>
         |
         v
  Typed structs (TerminalConfig, PowerConfig)
         |
         v
  Dispatch layer (connection.spl, controller.spl)
         |
         v
  Implementation modules (ssh_terminal, telnet_terminal, etc.)
```

Config is loaded once at startup (or on first MCP tool invocation via lazy loading). Named entries in SDN map to lookup by name in MCP tools:

```
terminal_connect(name: "test_host_ssh")
  -> find config by name in parsed list
  -> dispatch by kind
```

---

## 4. MCP Tool Registry Integration

The existing MCP server uses a lazy tool registration pattern:

1. **Tool table** (`src/app/mcp/tool_table.spl`): Static `McpToolEntry` definitions with name, description, input schema
2. **Protocol** (`src/lib/nogc_async_mut/mcp/main_lazy_protocol.spl`): JSON schema definitions for tool inputs/outputs
3. **Lazy server** (`src/lib/nogc_async_mut/mcp/main_lazy.spl`): Dispatches tool calls to handler functions

### Integration points:

```
tool_table.spl
  + 8 terminal McpToolEntry definitions
  + 6 power McpToolEntry definitions
  + 3 remote test McpToolEntry definitions

main_lazy_protocol.spl
  + 17 input/output JSON schemas

main_lazy.spl
  + import main_lazy_terminal_tools
  + import main_lazy_power_tools
  + import main_lazy_remote_test_tools
  + 17 new dispatch entries in tool_call handler
```

### Tool naming convention:

All new tools use descriptive prefixes to avoid collision with existing `t32_*` tools:
- `terminal_*` -- terminal operations
- `power_*` -- power control
- `relay_*` -- relay-specific operations
- `remote_test_*` -- remote test execution

---

## 5. Session Adapter Integration

The test daemon uses a session adapter pattern for different test execution environments:

```
SessionAdapter (interface via kind dispatch)
  kind 0-8: existing session kinds
  kind 9: SESSION_KIND_REMOTE_PC (new)
```

### Remote PC Adapter lifecycle:

```
start()    -> Open SSH/telnet terminal via terminal_connect
execute()  -> SSH exec "bin/simple test <path>" on remote host
health()   -> Check terminal connectivity (send echo command)
reset()    -> Disconnect + reconnect terminal
stop()     -> Close terminal via terminal_close
```

The adapter references a terminal config name and optionally a power config name. If power config is provided, `start()` also powers on the target, and `stop()` powers it off.

---

## 6. Dependency Diagram

```
                    +------------------+
                    |   SDN Config     |
                    | t32_terminal.sdn |
                    +--------+---------+
                             |
                     +-------v--------+
                     | config_parser  |
                     +---+-------+----+
                         |       |
              +----------+       +----------+
              |                             |
     +--------v--------+          +--------v--------+
     | TerminalConfig  |          |  PowerConfig    |
     +--------+--------+          +--------+--------+
              |                             |
     +--------v--------+          +--------v--------+
     |  connection.spl |          | controller.spl  |
     | (term dispatch) |          | (power dispatch)|
     +--+--+--+--+-----+          +--+--+--+-------+
        |  |  |  |                   |  |  |
        v  v  v  v                   v  v  v
      SSH Tel SWD Relay           T32 Relay Host
       |        |                  |
       v        v                  v
   ssh_ffi  Trace32Client     Trace32Client
       |        |
       v        v
    libssh2  T32 RCL (TCP)

     +------------------+
     |  credential/     |
     |  store.spl       |
     +--------+---------+
              |
     +--------v--------+
     |   AES-CBC +     |
     |   BCrypt KDF    |
     +-----------------+

     +--------------------+       +---------------------+
     | MCP Tool Handlers  |       | Remote PC Adapter   |
     | (17 new tools)     |       | (session kind 9)    |
     +--------+-----------+       +----------+----------+
              |                              |
              v                              v
     Terminal dispatch +            Terminal dispatch +
     Power dispatch                 Power dispatch
```

---

## 7. Key Design Decisions

### 7.1 Kind-Based Dispatch over Interface Traits

**Decision:** Use integer kind constants and `match` statements for all dispatch.
**Rationale:** Project rule prohibits inheritance. Traits could work but add complexity for a small number of kinds (3-4 per dispatch). Match statements are explicit and easy to extend.

### 7.2 .shs Script Abstraction for Relays

**Decision:** Relay control delegates to user-provided `.shs` scripts rather than implementing vendor protocols.
**Rationale:** Relay hardware is diverse (USB HID, serial, GPIO, smart PDU). Script abstraction supports any hardware without code changes. Users write thin scripts wrapping their specific relay commands.

### 7.3 Credential Encryption with Local Master Key

**Decision:** AES-CBC encryption with a local master key file (`~/.simple/credential_key`).
**Rationale:** Passwords must not appear in plaintext in SDN config files (which may be committed). A local master key is simple, requires no external key management service, and is sufficient for development/lab environments.

### 7.4 Lazy Loading for MCP Tools

**Decision:** New MCP tool handlers are lazily imported (loaded on first invocation).
**Rationale:** Matches existing pattern. Users who don't use terminal/power features pay no startup cost.

### 7.5 Separate Config File

**Decision:** Terminal/power config in `config/t32/t32_terminal.sdn`, separate from existing T32 debug config.
**Rationale:** Avoids modifying existing T32 configuration. Terminal and power are logically distinct from debug/trace even though they share the T32 connection.
