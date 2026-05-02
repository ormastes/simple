<!-- codex-research -->
# Local Research — `tmux_simpleos`

Date: 2026-04-24

## Scope

Question: should SimpleOS support `tmux` by:

1. porting it to Simple, or
2. loading a stock/bundled binary from the filesystem?

## Relevant Existing Surfaces

### 1. Host-side `std.tmux` already exists, but it is not an OS implementation

`src/lib/nogc_sync_mut/tmux/mod.spl` implements `std.tmux`.

Key observation:

- It shells out to host commands such as `tmux list-sessions`, `tmux send-keys`,
  and `tmux capture-pane`.
- It depends on `std.io_runtime.shell`, not on a SimpleOS kernel/session layer.
- The repo already models the tmux object hierarchy:
  - `TmuxSession`
  - `TmuxWindow`
  - `TmuxPane`
  - `TmuxCaptureResult`

Implication:

- The existing API is a useful behavioral reference.
- It does **not** prove that SimpleOS can run `tmux` internally.

### 2. A dashboard API for tmux also already exists, but assumes host tmux

`src/app/web_dashboard/tmux_api.spl` exposes `/api/tmux/*`.

Key observation:

- Requests are routed to `std.tmux`.
- If tmux is missing, the API returns `503`.
- This is a host-integration layer, not a SimpleOS-native session manager.

Implication:

- There is already an app/UI contract we can preserve if we build a native
  multiplexer later.

### 3. SimpleOS shell is already substantial

`src/os/apps/shell/shell_app.spl` and `test/system/os_shell_spec.spl`.

Observed capabilities:

- built-in commands
- job control (`cmd &`, `jobs`, `fg`, `bg`)
- pipelines
- file redirection
- async command execution
- VFS-backed execution and PATH lookups

Implication:

- A native multiplexer does not need to invent shell semantics first.
- There is already a command interpreter suitable for panes.

### 4. Filesystem-backed executable loading exists

`src/os/kernel/loader/executable_source.spl` and
`test/os/kernel/loader/executable_source_vfs_spec.spl`.

Observed capabilities:

- resolve executable bytes from initramfs
- fall back to VFS-backed bytes
- resolve seeded `/sys/apps/...` app paths
- support SMF-wrapped executables

Implication:

- SimpleOS can already locate executables from the filesystem.
- This is necessary but not sufficient for stock `tmux`.

### 5. Process spawn/exec exists, but the contract is still narrow

`src/os/sosix/process.spl`, `doc/08_tracking/feature.md`.

Observed capabilities:

- `fork`
- `execve`
- `spawn binary from path bytes`
- `waitpid`
- `signal`

Important gaps from tracking/docs:

- many exec features are still partial or platform-specific
- live proof is strongest on x86_64 and narrower elsewhere
- shell/process/UI parity is not complete across all SimpleOS lanes

Implication:

- Running any external Unix program is still an evolving substrate.
- This raises the risk of trying to host unmodified `tmux` too early.

### 6. PTY support exists, but only as an SSH-local emulation layer

`src/os/apps/sshd/ssh_pty.spl`, `src/os/apps/sshd/ssh_session.spl`,
`doc/09_report/simpleos_status_2026-04-04.md`.

Observed design:

- PTY is implemented using two POSIX pipes
- SSH writes decrypted input into the master side
- shell reads and writes through the slave side
- resize handling updates rows/cols only

Important limitation:

- This is a narrow in-process PTY abstraction for SSH shell sessions
- not a general Unix PTY subsystem with controlling terminal semantics

Implication:

- It is a strong starting point for a native multiplexer
- it is **not** enough evidence that stock tmux can run unchanged

## What `tmux` Needs Versus What Exists

### Already present enough for a native Simple implementation

- session/window/pane data model
- shell process orchestration
- pipe-based pane I/O
- resize propagation
- remote/dashboard API patterns

### Missing or weak for an unmodified stock-binary path

- general-purpose PTY subsystem
- controlling terminal/session semantics
- stronger Unix compatibility around terminal behavior
- build/runtime dependency story for `libevent`, `ncurses`, and libc surface
- proof that terminal escape handling and UTF-8 behavior are correct enough

## Local Conclusion

Based on the current repo:

- **Porting or reimplementing a tmux-like multiplexer in Simple is realistic.**
- **Running stock tmux as a bundled filesystem-loaded binary is higher risk and
  likely blocked on Unix compatibility gaps outside simple executable loading.**

Recommended local direction:

1. build a native `simplemux`/`tmux-lite` service first
2. keep the existing `std.tmux` / REST shape as the compatibility-facing API
3. treat stock tmux binary hosting as a later compatibility milestone after
   PTY and exec semantics are promoted from app-local helpers to OS services
