# Unix `rt_pty_spawn` exec'd a whole command line as one path (2026-11-14)

**Symptom (macOS 26.5 arm64, same code path on Linux/BSD):** every smux pane
spawned with arguments (`/bin/sh -i`) was dead on arrival: spawn returned a pid,
`is_running` false, reads empty, `smux_send_command` -> `write failed: <pane>`.
Windows was unaffected because `CreateProcess` parses the command line.

**Root cause:** `pty_process::spawn` (`src/compiler_rust/runtime/src/value/pty.rs`)
and its interpreter twin `pty_spawn`
(`src/compiler_rust/compiler/src/interpreter_extern/pty.rs`) called
`execvp(<entire text>, [basename])`, so `"/bin/sh -i"` was looked up as a file
named `/bin/sh -i` and the child exited 127.

**Fix:** the direct exec is kept (a bare path, even one with spaces, behaves as
before); when it fails the child runs `/bin/sh -c "exec <line>"`, so the one PTY
interface (`std.sosix.pty`) accepts the same command text on every platform.
Also: Caret's two direct `std.sys.pty` imports (`tui_io.spl`, `cs_main.spl`) now
go through `std.sosix.pty`, the single PTY entry point.

**Specs**
- Reproducer: `test/01_unit/os/apps/smux/pane_cooked_read_enter_spec.spl`
  (0/2 with a 15 s timeout before, 2/2 in ~2 ms after, on macOS).
- Generalization: `test/01_unit/os/apps/smux/pane_readline_typed_input_latency_spec.spl`
  (3/4 -> 4/4) and Rust unit test
  `rt_pty_spawn_accepts_a_command_line_with_arguments` in `value/pty.rs`.

**BSD:** same Unix branch; `/bin/sh` and `execv` are POSIX, so FreeBSD gets the
same fix. Not run on the FreeBSD VM.
