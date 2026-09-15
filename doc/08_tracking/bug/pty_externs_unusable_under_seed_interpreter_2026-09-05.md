# PTY externs are unusable under the seed interpreter, and their declarations disagree with the runtime

> **RESOLVED 2026-09-05 (lane A10).** Root cause found, fixed, and proved with a
> tty-vs-pipe contrast. Read this block before the historical text below.
>
> **Root cause (§2's `-1`): `rt_pty_spawn` in `src/compiler_rust/runtime/src/value/pty.rs`
> declared its `shell` parameter as `*const c_char`, and a Simple `text` argument
> arrived there as an EMPTY C string** — so `spawn` fell out at its
> `shell.is_empty()` guard and returned the catch-all `-1` with no diagnostic.
> Its own sibling in the same file, `rt_pty_write`, already took a `RuntimeValue`
> for a Simple `text`; `rt_pty_spawn` was the odd one out. It now takes
> `RuntimeValue` too and decodes via `runtime_value_to_string`.
>
> The bug doc's earlier "two independent SLAVE_TABLEs" guess was **wrong as the
> cause but right as a hazard**: `rt_pty_spawn` dispatches to the RUNTIME
> `#[no_mangle]` symbol, not to the interpreter extern table, even though the
> latter registers the name — the JIT resolves the symbol first. Both copies now
> fall back to `ptsname(master_fd)` when the table misses, so a split
> open/spawn pair can no longer produce a silent failure, and both return
> distinct codes (-2 no slave, -3 bad shell string, -4 fork failed, -5 empty
> shell, -6 non-string shell value) instead of a single ambiguous -1.
>
> §1 fixed: `rt_pty_read`, `rt_pty_write` and `rt_pty_close` are now registered in
> `interpreter_extern/mod.rs` with interpreter-mode implementations in
> `interpreter_extern/pty.rs`, and those interpreter implementations are the LIVE
> path — measured, not assumed. `build/nb/fixtures/probe_pty_dispatch.spl` calls
> all three on fd -1 and gets `read=[] write=false close=false` with **no**
> `PTY read error: failed to get flags` / `PTY write error:` on stderr; those
> strings are what the runtime copies print on exactly that input. So dispatch
> splits by signature: `rt_pty_open`/`rt_pty_spawn` reach the runtime
> `#[no_mangle]` symbols, while the `text`/`bool`-returning `rt_pty_read`,
> `rt_pty_write` and `rt_pty_close` go through the interpreter extern table.
>
> §3 fixed: `src/os/apps/smux/smux_remote.spl` declarations now match the real
> ABI, and `smux_remote.spl:117`'s `if written >= 0:` on a bool is gone.
>
> §4 done: `src/os/apps/smux/api.spl` gained an OPT-IN PTY lane
> (`smux_pane_spawn_pty` / `smux_pane_is_pty` / `smux_pane_close_pty`, plus a
> `pty_fd` field on `PaneRecord`). The pipe lane is unchanged and still the
> default; all seven pre-existing smux specs stay green.
>
> **Evidence — the same two commands through both lanes, one process**
> (`build/nb/fixtures/probe_pty_tty.spl`, binary
> `src/compiler_rust/target/debug/simple`, 119,938,520 bytes, Sep 5 21:10):
>
> ```
> === A. PTY lane (rows=31 cols=97) ===
> pty_open_fd=4
> pty_spawn_pid=28949
> pty_write_ok=true,true
> PTY_OUT_BEGIN
> tty
> stty size
> sh-3.2$ tty
> /dev/ttys031
> sh-3.2$ stty size
> 31 97
> sh-3.2$
> PTY_OUT_END
> === B. pipe lane (same two commands) ===
> pipe_spawn_pid=29455
> stty: stdin isn't a terminal
> PIPE_OUT_BEGIN
> not a tty
> PIPE_OUT_END
> ```
>
> `/dev/ttys031`, the kernel-reported `31 97` (exactly the winsize passed to
> `openpty`), and the interactive `sh-3.2$` prompt are all things a pipe cannot
> produce; the pipe run says `not a tty`. Neither expected string appears in the
> input, so the PTY's own ECHO cannot fake either result.
>
> **Still open (NOT fixed here):** there is still no C-runtime PTY lane
> (`src/runtime/runtime_pty.c` is compiled by no build path), so a pure-Simple
> NATIVE build still has no PTY. The lane above works under the interpreter/JIT
> runner only.

## Historical record (as filed)

- **Filed:** 2026-09-05
- **Host:** macOS arm64 (Darwin 25.5.0)
- **Binary:** `src/compiler_rust/target/bootstrap/simple` (130,402,384 bytes, Sep 5 20:01)
- **Blocks:** routing smux panes through a real PTY (MUX-H001 upgrade path).
  smux panes are on pipes instead — see `src/os/apps/smux/api.spl` header.

## 1. `rt_pty_read` / `rt_pty_write` are backed by nothing in the interpreter

`src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2803-2804` registers
exactly two PTY names:

```
insert_simple!("rt_pty_open", pty::rt_pty_open);
insert_simple!("rt_pty_spawn", pty::rt_pty_spawn);
```

`rt_pty_read`, `rt_pty_write` and `rt_pty_close` exist only as `#[no_mangle]`
symbols in `src/compiler_rust/runtime/src/value/pty.rs` (the compiled/native
path). Calling them from interpreted Simple yields:

```
rt_interp_call error: ... "unknown extern function: rt_pty_write" ... code: Some("E-SFFI-001")
warning: extern `rt_pty_write` (argc=2) is declared but backed by no implementation
         -- the call returned nil ...
```

Probe: `build/nb/fixtures/probe_pty3.spl` →
`open_fd=4`, `write_val=false`, `read_is_nil=true`, `read_val=[nil]`.

## 2. `rt_pty_spawn` returns -1 on this host even though `rt_pty_open` succeeds

`build/nb/fixtures/probe_pty2.spl`:

```
A_open_fd=4
A_spawn=-1
B_open_fd=6
B_spawn_intlit=-1
```

Two fresh master fds, both `spawn` calls fail. `pty_spawn` returns -1 only for
an empty shell string, a `SLAVE_TABLE` miss, a `CString` error, or `fork() < 0`.
Root cause not isolated; the most likely candidate is that `rt_pty_open` and
`rt_pty_spawn` do not share one `SLAVE_TABLE` (there are two independent copies,
one in `interpreter_extern/pty.rs` and one in `runtime/src/value/pty.rs`), so a
mixed dispatch loses the slave fd. **Not root-caused in this lane.**

## 3. The declarations in `src/os/apps/smux/smux_remote.spl:22-30` are wrong

| declared (`smux_remote.spl`) | actual (`runtime/src/value/pty.rs`) |
|---|---|
| `rt_pty_read(fd: i32, buf_size: i32) -> text` | `rt_pty_read(fd: i64, timeout_ms: i64) -> RuntimeValue` — the second argument is a **timeout in milliseconds**, not a buffer size, so `rt_pty_read(fd, 4096)` blocks up to 4 s |
| `rt_pty_write(fd: i32, data: text) -> i32` | `rt_pty_write(fd: i64, data: RuntimeValue) -> RuntimeValue` — returns a **bool**, so `smux_remote.spl:117`'s `if written >= 0:` compares a bool against 0 |
| `rt_pty_spawn(master_fd: i32, shell: text) -> i64` | `rt_pty_spawn(master_fd: i32, shell: *const c_char) -> i64` |

Left unedited deliberately: fixing the declarations without fixing (1) and (2)
would only change which wrong answer is returned.

## Unblock condition

1. Register `rt_pty_read` / `rt_pty_write` (and `rt_pty_close`) in
   `interpreter_extern/mod.rs`, sharing ONE slave-fd table with `rt_pty_open`.
   Note that adding `rt_pty_close` as a new Simple `extern` declaration must be
   checked against `scripts/check/unbacked_extern_baseline.txt` first.
2. Root-cause the `rt_pty_spawn` -1 on macOS arm64.
3. Correct the declarations in `smux_remote.spl` to the real ABI.
4. Then move `smux_pane_spawn` in `src/os/apps/smux/api.spl` from
   `process_spawn_piped` to the PTY, and the pipe path becomes the fallback.

Until then a smux pane has no controlling terminal: line-oriented children work
(proved by `test/01_unit/os/apps/smux/smux_terminal_service_spec.spl`), curses
apps and interactive shells will not.

Separately: there is **no C-runtime PTY lane at all** (`src/runtime/runtime_pty.c`
is no longer compiled by any build path, per `interpreter_extern/pty.rs`'s own
header), so a pure-Simple native build has no PTY regardless of the above.
