# smux specs red on macOS (arm64): stale limit, Windows-only fixtures, missing Unix provider

Status: PARTLY FIXED. Host: macOS 26.5 arm64, Rust seed built from
`release/1.0.0` `d1ba435a0b3` plus the Unix `rt_pty_spawn` command-line fix.
All counts below are from that seed, run in this tree.

## Fixed

| Spec | Before | After | Root cause |
|---|---|---|---|
| `test/03_system/tools/smux_protocol_features_spec.spl` | 57/58 | 59/59 | Stale spec. `REPLY_LIMIT` in `src/os/apps/smux/server.spl:45` was raised from 65536 to 1048576 (`ca2a853ca55`); the example still declared 65537 and expected an over-limit refusal. Not host-specific. |
| `test/03_system/tools/smux_pane_lifecycle_spec.spl` | 10/12 | 12/12 | The two real-child cases hardcoded `cmd.exe /Q` and `set /a`. The closure contract is host-neutral, so the shell and the sum command now come from the host (`sosix_pty_default_shell()`, `expr`). |
| `test/03_system/tools/smux_presentation_native_spec.spl` | 0/2 | 2/2 | Hardcoded `cmd.exe /d /q` and a PowerShell `[Console]::WindowWidth` probe. Non-Windows hosts now measure the viewport with `stty size` in the SOSIX default shell. Every dimension assertion is unchanged. |
| `test/01_unit/os/apps/smux/server_large_reply_drain_spec.spl` | exit 1, 0 executed | exit 0, 1 passed + 1 pending | Its only example goes through the Caret workspace, whose backend is smux on Windows only (`src/app/llm_caret/agent_workspace.spl:105`), so it was pending and the runner failed the file for zero executed examples. A second example starts the same owner program directly and checks the same 400 KB reply. |

Reproducing cases: the examples named above. Generalization cases:
"should admit a declared body length up to the response limit as a length"
(limit boundary and the former limit), and the direct-owner large-reply example
(the owner reply path on a host the workspace example never reaches). The
lifecycle and presentation specs each cover both a piped/PTY or a Cells/Percent
variant of the ported fixture.

No source under `src/` changed: the pane, resize, capture and owner paths
already work on macOS through `std.sosix.pty`.

## Still red, and why

### `smux_literal_input_spec.spl` (0/3), `smux_configured_launch_spec.spl` (0/3)

Not macOS-specific; the same specs are recorded red on Windows under the seed in
`smux_native_provider_lane_blocked_on_windows_seed_2026-10-31.md`. Three
independent blockers:

1. Fixtures. They require `SIMPLE_TEST_LITERAL_CHILD`,
   `SIMPLE_TEST_CONFIGURED_CHILD`, `SIMPLE_TEST_CONFIGURED_CWD`,
   `SMUX_CONFIGURED_REMOVE` and `SMUX_CONFIGURED_KEEP`, naming natively compiled
   `test/fixtures/coremux/{literal_input,configured_launch}_child.spl`. Nothing
   builds those or sets the variables on any host (first failing lines:
   literal `:119`, configured `:124`).
2. No Unix structured-launch or literal-byte provider. The interpreter resolves
   `std.sosix.pty` to `src/lib/sys/pty.spl`, where `spawn_configured_v1` (`:23`),
   `configured_launch_probe_v1` (`:29`), `literal_bytes_supported_v1` (`:33`),
   `write_literal_some_v1` (`:36`) and `exit_code` (`:44`) refuse. The only real
   provider is the Windows overlay `src/providers/windows_native/lib/sys/pty.spl`.
   The runtime ABI behind the portable provider is `rt_pty_spawn(handle, text)`
   and `rt_pty_write(handle, text)`: it cannot carry argv, cwd, environment
   changes, or the octets 0x00/0x80/0xff.
3. The configured Shell example (`:150`) uses Windows shell syntax
   (`&&ping -n 16 127.0.0.1 >nul`).

Unblock: add byte-preserving write and argv/cwd/env exec to the Unix `rt_pty_*`
lane (both `src/compiler_rust/runtime/src/value/pty.rs` and
`src/compiler_rust/compiler/src/interpreter_extern/pty.rs`), implement the five
functions above over them in `src/lib/sys/pty.spl`, and add a lane that builds
the two fixtures and exports the variables. A shell-prefix emulation in pure
Simple was not used: `src/lib/sys/pty.spl:21-22` and
`pane_configured_launch_service.spl:52-53` forbid it.

### `test/03_system/app/llm_caret/feature/smux_runtime_terminal_transport_spec.spl` (0/1)

`semantic: unknown extern function: rt_process_spawn_piped_generation_v1`. The
call is `src/lib/nogc_sync_mut/io/process_ops.spl:2314` (the reported
`spec.spl:2314` location is misattributed). The whole `PipedProcessRefV1`
family (`rt_process_*_ref_v1`, declared `process_ops.spl:2122-2137`) exists only
in the C runtime (`src/runtime/runtime_process.c:2387` and following); the Rust
runtime and interpreter extern table have no such symbols, so the spec cannot
run under the seed on any host. Unblock: a Rust twin of that generation-checked
registry, or a self-hosted binary linked against the C runtime.
