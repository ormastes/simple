# cs_main.spl cannot safely JIT: three seed JIT defects (2026-10-04)

Status: OPEN (seed). cs stays on the interpreter fallback until these are fixed.

## How cs gets de-JITted (source-side, fixable)

`bin/cs` logs `[jit-fallback] HIR lowering error: Cannot infer field type:
struct 'ANY' field 'status'`. Bisected (import-one-module probes) to
`src/lib/nogc_async_mut/sosix/fs.spl:226` — `value.status` where `value` comes
from `SimpleRing<SosixFileOperation, SosixCompletion>.take_completion_retained`,
whose `Cpl` generic erases to ANY. A typed intermediate
(`val sc: SosixCompletion = value`) clears it. The next blocker is
`src/lib/nogc_sync_mut/tui/terminal.spl:273` — free-function
`substring(content, 0, width)` is an unresolved JIT symbol; `content.substring(0, width)`
clears it. With both, cs_main.spl JIT-compiles with no `[jit-fallback]`.

Both edits were deliberately BACKED OUT, because the JIT-compiled cs is wrong:

## Defect 1 — `.trim_end()` / `.trim_start()` emit unresolved `str.X`

Minimal repro (JIT default, seed `src/compiler_rust/target/release/simple`):

```
use app.io.mod.{env_get}
use std.nogc_async_mut.sosix.{sosix_which}
fn rt(s: text) -> text:
    s.trim_end()
fn main():
    print "[" + rt("ab  ") + "]"
main()
```

-> `Runtime error: Function 'str.trim_end' not found` (exit 70). Same for
`trim_start`; `trim` works. Without the two imports it prints `[ab]`. The
builtin map in `compiler/src/codegen/instr/calls.rs` (~3818) has the arm, so a
large co-compiled closure is routing the call down a different path. In cs this
aborts the process at the first `vt_text` (`src/os/apps/smux/vt_screen.spl`).

## Defect 2 — JIT-compiled code does not reclaim temporaries

Same loop, `cs_frame_rows(d, 200, 50, "00:00", true)` for 20 s:
- interpreter: RSS flat at 220 MB, ~130 frames/s
- JIT: ~750 frames/s, RSS 657 MB -> 1.91 GB in 12 s (~130 KB per frame)

A `pty_read(0, 0)` loop also grows ~1.1 MB/s under JIT. The live JIT cs grew
~130 KB/s idle and ~4 MB/s with one agent (331 -> 452 MB in 10 s).

## Defect 3 — smux pane liveness wrong under JIT

`pane_spawn_at("cslive", "z1", "/bin/sleep", ["20"], ...)` then `pane_list`:
interpreter lists 1 pane, JIT lists 0 (child alive). Path:
`_smux_list` -> `smux_pane_alive` -> `_child_alive` -> `pty_is_running`
(`rt_pty_is_running` is in the `hybrid-interp-splice` list). The live JIT cs
showed a running agent as `gone: pane closed`.

## Unblock condition

All three repros behave as under `SIMPLE_EXECUTION_MODE=interpreter`; then
re-apply the two source edits above and repeat the live cs check (launch,
/switch, chat, /kill, relaunch, /agents, resize) against the interpreted run.
