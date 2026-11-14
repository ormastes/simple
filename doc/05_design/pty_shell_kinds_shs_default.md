# PTY shell kinds: the Simple shell (shs) beside the native shell

Status 2026-11-14: phase 1 landed and verified on macOS 26.5 arm64. Phases 2-3 are open.

## 1. Problem

A pane's shell was whatever the host had: `/bin/sh` on Unix, `cmd.exe` on
Windows. Every caller that typed into a pane (smux specs, Caret agents) needed a
per-platform branch (`set /a` vs `$((..))`, PowerShell vs `stty`). SimpleOS has
no interpreter for native scripts at all, so a native-only PTY cannot serve it.

## 2. Decision

The PTY names a **shell kind** instead of a program:

| Kind | Program | Where |
|---|---|---|
| `shs` | the Simple shell — `os.apps.shell` `ShellApp`, the shell SimpleOS boots | every OS; the only kind on SimpleOS |
| `native` | `/bin/sh`, `cmd.exe` | hosts only; refused on SimpleOS (`pty-shell-native-unavailable-on-simpleos`) |

One interface for every platform, under SOSIX (`std.sosix.pty`):

- `sosix_pty_shell_command_v1(kind) -> Result<text, text>` — the command line for a kind.
- `sosix_pty_default_shell() -> text` — the command for the selected kind.
- `SOSIX_PTY_SHELL_SHS`, `SOSIX_PTY_SHELL_NATIVE`.

Selection lives in `src/lib/sys/pty_shell.spl` as pure text functions
(`pty_shell_command_for_v1`, `pty_shell_kind_for_v1`, `pty_default_shell_for_v1`);
spawning is unchanged in `std.sys.pty`. smux's four default-shell call sites
(`smux_app`, `smux_remote`, `interactive_protocol`) already call
`sosix_pty_default_shell`, so they follow the selection with no edit.

## 3. Hosted shs

`src/app/shs/main.spl` runs `ShellApp` on a host's stdin/stdout, so the same
shell and builtins answer in a host PTY:

    simple src/app/shs/main.spl

The launcher a host uses for `shs` is `SIMPLE_SHS_COMMAND` verbatim, else
`$SIMPLE_BINARY <cwd>/src/app/shs/main.spl` when that entry exists. On SimpleOS
`shs` is `/sys/apps/shell`.

## 4. Default kind

| Platform | Default | Override |
|---|---|---|
| SimpleOS | `shs` (no alternative) | none |
| Windows, macOS, Linux, BSD | `native` | `SIMPLE_PTY_SHELL=shs` |

A host that asks for `shs` but has no launcher gets its native shell rather than
a dead pane. SimpleOS never falls back to native.

**Why hosts are not `shs` by default yet.** Measured on macOS: hosted shs has no
host filesystem (`ls`, `cat` answer "no filesystem mounted"), cannot start host
programs (`git` -> "command not found"), and does not expand variables. Making
it the default would take those away from every smux pane and Caret agent. The
flip is one line in `pty_shell_kind_for_v1` once phase 2 lands.

## 5. Phases

1. **Done.** Shell kinds and selection; hosted shs entry; smux pane on shs
   through the real PTY; `exit` fixed (it called a method `OsExecutor` never had).
2. **Open — host parity for shs.** A host-backed VFS for `ShellApp.with_vfs`
   and host program launch through SOSIX process, then flip the host default.
3. **Open — SimpleOS PTY provider.** `rt_pty_*` exists only in the host Rust
   lane. SimpleOS needs a provider under the same `std.sys.pty` surface that
   attaches `ShellApp` to a pane; it must be shown on QEMU real firmware and on
   the board (`.claude/rules/board-runnable.md`). Not started.

## 6. Tests

- `test/01_unit/lib/sys/pty_shell_spec.spl` — selection per platform, the
  SimpleOS refusal, host fallback.
- `test/03_system/tools/smux_shs_pane_spec.spl` — a real smux pane on hosted
  shs: `expr 40 + 2` -> `42`, `exit` -> `logout`.
