# PTY shell kinds: the Simple shell (shs) beside the native shell

Status 2026-11-14: phases 1 and 2 landed and verified on macOS 26.5 arm64;
hosts now default to `shs`. Phase 3 is open.

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

`src/app/shs/main.spl` runs `ShellApp.hosted_on_host()` on a host's
stdin/stdout, so the same shell and builtins answer in a host PTY:

    simple src/app/shs/main.spl

The launcher a host uses for `shs` is `SIMPLE_SHS_COMMAND` verbatim, else
`$SIMPLE_BINARY <cwd>/src/app/shs/main.spl` when that entry exists. On SimpleOS
`shs` is `/sys/apps/shell`.

Host parity (`src/os/apps/shell/shell_host.spl`, `ShellApp.hosted == true`):

- **Host VFS.** `HostFilesystem` implements the VFS `Filesystem` trait over
  std fs (`std.nogc_sync_mut.io_runtime`) and is mounted at `/`, so `ls`,
  `cat`, `cd`, `mkdir`, `rm`, `mv` hit the real host tree. The shell starts in
  the host cwd, and `cd` also moves the process cwd so launched programs see it.
- **Host programs.** A command that is not a builtin runs through the SOSIX
  process facade (`sosix_process_run_bounded`, host PATH), its stdout/stderr
  written to the pane and its exit status kept in `$?`. SimpleOS guest artifact
  gates and staged-toolchain shims are skipped on a host.
- **Environment.** The shell env is seeded from the host environment; every
  argument gets `$VAR` / `${VAR}` / `$?` expansion; `export` also sets the
  process env so children inherit it.
- System builtins that would answer about the SimpleOS guest (`uname`,
  `hostname`, `uptime`, `ps`, `kill`, `date`, `dmesg`, `mount`) run the host
  program instead; `reboot` refuses. Missing commands report `command not
  found` with status 127.

Known gaps (hosted only; `SIMPLE_PTY_SHELL=native` covers them):

- Pipelines, redirections and `&` are refused with status 2 — they still go
  through the SimpleOS fd/spawn layer, which killed the process on a host.
- Host programs run captured (`sosix_process_run_bounded`: no stdin/TTY,
  10-minute timeout, 16 MB output cap), so interactive programs (editors,
  pagers, REPLs) do not work in a shs pane.
- The tokenizer drops quote kind, so `'$X'` still expands.
- Windows is unverified: the host VFS is rooted at `/` and path resolution
  assumes `/`-absolute paths, so a drive-letter cwd likely breaks `cd`/`ls`.

## 4. Default kind

| Platform | Default | Override |
|---|---|---|
| SimpleOS | `shs` (no alternative) | none |
| Windows, macOS, Linux, BSD | `shs` | `SIMPLE_PTY_SHELL=native` |

A host whose shs launcher is unresolved gets its native shell rather than a
dead pane. SimpleOS never falls back to native.

## 5. Phases

1. **Done.** Shell kinds and selection; hosted shs entry; smux pane on shs
   through the real PTY; `exit` fixed (it called a method `OsExecutor` never had).
2. **Done.** Host parity for shs (section 3) and the host default flipped to
   `shs` in `pty_shell_kind_for_v1`.
3. **Provider landed, hosted-tested only (2026-11-14); QEMU/board unverified.**
   `rt_pty_*` exists only in the host Rust lane. `src/os/apps/shell/pty_provider.spl`
   exposes the `std.sys.pty` surface (`open`, `spawn`/`spawn_v1`, `write`,
   `read`, `is_running`, `close`, `platform_default_shell`) over a handle table
   of in-process `ShellApp`s. `spawn` admits only `PTY_SHS_SIMPLEOS_COMMAND`
   (`/sys/apps/shell`); any other program is
   `Err("pty-native-spawn-unavailable-on-simpleos: ...")` — SimpleOS has no
   native-script interpreter. `write` -> `feed_remote_input`, `read` ->
   `take_remote_output` (non-blocking; the shell runs synchronously inside
   `write`, so `timeout_ms` is not waited on), shell `exit` -> `is_running`
   false and later writes refused. It lives in the OS layer, not `src/lib`,
   because std must not import `os.apps.*`; a SimpleOS image selects it by
   importing it in place of `std.sys.pty`. Open: a SimpleOS pane consumer wired
   to it, resize, and the QEMU real-firmware (OVMF) and board runs required by
   `.claude/rules/board-runnable.md` — tracked in
   `doc/08_tracking/todo/simpleos_pty_provider_unverified_2026-11-14.md`.

## 6. Tests

- `test/01_unit/lib/sys/pty_shell_spec.spl` — selection per platform (shs
  default, native opt-out), the SimpleOS refusal, host fallback.
- `test/01_unit/os/apps/shell/shell_host_spec.spl` — host VFS (`ls`/`cat`/`cd`,
  missing dir), host program output and exit status, `$VAR` expansion and
  `export` inheritance.
- `test/03_system/tools/smux_shs_pane_spec.spl` — a real smux pane on hosted
  shs: default selection, `expr 40 + 2` -> `42`, `pwd` = host cwd, an exported
  variable through a host `sh`, `exit` -> `logout`.
- `test/01_unit/os/apps/shell/pty_provider_spec.spl` — the SimpleOS provider
  driven on host: spawn `/sys/apps/shell`, `expr 40 + 2` -> `42`, `exit`
  stops the handle; other programs refused.
