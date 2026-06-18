# Design: Pure Simple SSH and HTTPS Servers

## Goal

Implement a boundary-first release slice where SSH and HTTPS release-mode server
entrypoints choose Simple protocol code and delegate only OS access to runtime
or SFFI adapters.

## Data Structures

`PureServerMode`:

- `Alpha`
- `Beta`
- `Release`

`PureServerHostTarget`:

- `HostedLinux`
- `SimpleOS`

`PureServerProtocol`:

- `SSH`
- `HTTPS`

`PureServerHostAccessCaps`:

- `target`
- `can_accept_tcp`
- `can_read_write_tcp`
- `can_load_files`
- `can_get_entropy`
- `can_spawn_process`

`PureServerRouteDecision`:

- `protocol`
- `mode`
- `target`
- `uses_simple_protocol`
- `allows_native_protocol_bypass`
- `host_access_summary`

## Algorithms

### Mode Decision

1. Parse or receive a mode name.
2. Normalize accepted release spellings to `release`.
3. Reject unknown mode names.
4. For `release`, set `uses_simple_protocol=true` and
   `allows_native_protocol_bypass=false`.
5. For `alpha` and `beta`, set `uses_simple_protocol=true` and allow a
   comparison path only if a compatibility/native path is explicitly configured.

### Host Access Validation

1. SSH requires TCP accept/read/write, entropy, and process execution.
2. HTTPS requires TCP accept/read/write, entropy, and certificate/key file
   loading.
3. Hosted Linux and SimpleOS adapters must satisfy the same protocol-facing
   capability checks.
4. Missing capabilities fail closed with a typed diagnostic.

### Release Entrypoint Routing

1. Build `PureServerRouteDecision`.
2. Validate required host access for the selected protocol.
3. Call the protocol module path for SSH or HTTPS.
4. Never call native protocol SFFI wrappers in release mode.

## Initial Implementation Slice

Add a small shared policy module that encodes mode, target, protocol, host
capabilities, validation, and route decision. Then wire SSH/HTTPS wrappers to
use that policy before deeper server integration.

## Error Handling

Use `Result<T, text>` for mode parsing and capability validation. Diagnostics
must name the missing capability and protocol.

## Tests

- Release mode rejects native protocol bypass for SSH.
- Release mode rejects native protocol bypass for HTTPS.
- Hosted Linux and SimpleOS can both satisfy the required capability records.
- Missing process execution fails SSH validation.
- Missing certificate/key file access fails HTTPS validation.
- Unknown mode names return `Err`.

## Documentation Updates

Update SPipe/SFFI/RT guidance so future work treats runtime calls as host access
only and does not add full native protocol wrappers as release-mode shortcuts.
