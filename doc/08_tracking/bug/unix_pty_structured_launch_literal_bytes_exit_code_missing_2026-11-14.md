# Unix std.sys.pty refused structured launch, literal bytes and exit status

Status: FIXED (provider) 2026-11-14 — specs still partly red on the fixture
gate (see "Remaining"). Host: macOS 26.5 arm64, release/1.0.0 `f998bc43600`.

## Defect

`src/lib/sys/pty.spl` (the provider `std.sosix.pty` resolves to on every
non-Windows-native composition) refused `spawn_configured_v1`,
`configured_launch_probe_v1`, `literal_bytes_supported_v1`,
`write_literal_some_v1` and `exit_code`, because the only runtime ABI was
`rt_pty_spawn(handle, text)` / `rt_pty_write(handle, text)`: no argv, cwd,
environment changes or arbitrary octets.

## Fix

New externs, both Rust lanes, one shared implementation in
`src/compiler_rust/runtime/src/value/pty.rs`:

| extern | contract |
|---|---|
| `rt_pty_spawn_exec_v1(handle, program, args, cwd, env) -> pid` | literal `execve` (no shell fallback); argv after argv[0]; `cwd` "" inherits; env `+NAME=VALUE`/`-NAME` applied to a copy (parent env untouched); all C strings built before `fork`; chdir/exec failure exits 127 |
| `rt_pty_write_bytes_v1(handle, [u8]) -> n` | nonblocking raw write; 0 = queue full, -1 failure |
| (spawn failure) | a close-on-exec status pipe carries the child's chdir/exec errno; the parent reaps that child and returns -1, so no pane is published for a child that never reached its program |
| `rt_pty_exit_code_v1(handle) -> code` | exit code / 128+signal, -1 running, -2 no child; status is captured by whichever `waitpid` reaps it |

- Compiled lane: `rt_pty_*_v1` `#[no_mangle]` in `runtime/src/value/pty.rs`.
- Interpreter lane: `compiler/src/interpreter_extern/pty.rs` (records the child
  in that lane's own child table so close/is_running/hangup own it), registered
  in `interpreter_extern/mod.rs`.
- C lane: honest refusals in `src/runtime/runtime_process.c` (it owns no pty
  child table, same scope as its `rt_pty_hangup`).
- `src/lib/sys/pty.spl`: Unix implements the five functions; Shell mode is the
  SOSIX default shell's `-c`; Windows (portable ABI) still refuses explicitly.
- `smux_configured_launch_spec.spl:150`: Shell command ported to the host shell
  (`echo ... && sleep 15` off Windows); assertions unchanged.

**Requires a seed built from this tree.** The old shared seed reports
`unknown extern function: rt_pty_spawn_exec_v1`.

## Specs

| Spec | Before | After (new seed) |
|---|---|---|
| `smux_configured_launch_spec.spl` | 0/3 | 1/3 (Shell case green) |
| `smux_literal_input_spec.spl` | 0/3 | 0/3 |

| `sosix_pty_structured_launch_spec.spl` (new) | — | 2/2 |

Reproducing: the configured Shell example. Generalization (Simple, interpreter
lane): `test/03_system/tools/sosix_pty_structured_launch_spec.spl` — Exec with
a metacharacter argv, cwd, env Set + Remove, raw NUL/0x80/0xff, exit code 7;
and refusal of a missing cwd / program / invalid env name with the PTY still
spawnable afterwards. It caught a second defect: the interpreter passes `[u8]`
as packed `Value::ByteArray`, which the first cut rejected (-1). Generalization (Rust):
`value::pty::tests::pty_exec_request_is_literal_and_reports_exit_status`
(metacharacter argv, cwd, env set/remove, parent env untouched, raw
0x00/0x80/0xff through the PTY, exit code 7 after reap) and
`pty_exec_request_rejects_invalid_fields`,
`pty_spawn_exec_reports_chdir_and_exec_failure`. `cargo test -p simple-runtime
--lib value::pty`: 12 passed. Windows cfg arms were not compiled here.

## Remaining (unblock conditions)

1. Fixtures: nothing builds `test/fixtures/coremux/{configured_launch,literal_input}_child.spl`
   or exports `SIMPLE_TEST_*_CHILD` / `SIMPLE_TEST_CONFIGURED_CWD` /
   `SMUX_CONFIGURED_REMOVE` / `SMUX_CONFIGURED_KEEP`. The Exec and public-API
   configured examples and all three literal examples fail on that gate first.
2. `literal_input_child.spl` uses `std.sys.terminal_console`, whose portable
   provider (`src/lib/sys/terminal_console.spl`) refuses `open()` on every
   host, so even a built child exits 22 on Unix. Needs a Unix console provider.

BSD: the exec path is POSIX (`openpty`, `setsid`, `TIOCSCTTY`, `execve`,
`waitpid`), identical on FreeBSD; `cfmakeraw` in the test exists there too.
Not run on FreeBSD.
