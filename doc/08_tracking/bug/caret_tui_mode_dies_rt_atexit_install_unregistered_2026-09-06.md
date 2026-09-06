# Caret TUI mode dies instantly: `rt_atexit_install` missing from the interpreter extern registry

Date: 2026-09-06
Status: FIXED IN SOURCE — awaiting a seed deploy (see "Fix" below)
Area: `src/compiler_rust/compiler/src/interpreter_extern/terminal.rs` (Rust seed interpreter)

## Fix (2026-09-06)

Bridged in `interpreter_extern/terminal.rs` and registered in
`interpreter_extern/mod.rs`'s `EXTERN_DISPATCH`.

**A second unregistered extern was found while fixing this one, and it is not
described anywhere else:** `terminal_install_recovery()` calls
`rt_signal_install` on the line immediately after `rt_atexit_install`, and that
symbol had **zero** hits in `interpreter_extern/` too. Bridging only
`rt_atexit_install` would have moved the identical crash one line later.
`rt_signal_install` and `rt_signal_check` are therefore also bridged, with a
real `sigaction`-based handler plus an atomic flag array mirroring
`src/runtime/runtime.c:2650,2706-2730` — a stub would have silently broken
caret's terminal-resize handling instead of crashing honestly.

Verified with a privately-built binary (`CARGO_TARGET_DIR` under the scratchpad;
`bin/simple` deliberately NOT replaced — other sessions are using it). In a
tmux pane with `TERM=screen-256color` the caret TUI now stays alive for the full
40s poll window with zero `unknown extern function` lines on stderr, renders its
alt-screen frame, status bar and prompt, and exits cleanly on `/exit` rather
than crashing.

**Still required: someone must actually build and deploy the fixed seed.** Until
then every host still running the current `bin/simple` has the crash, which is
why the two `# ponytail:` ceilings in `chat_tui.spl` and `cs_main.spl` were left
in place.

## Symptom

`cs`'s `/launch caret` produces an agent that is dead on arrival. The dashboard
shows it as `exited: pane pid <N> is not running` with no actionable reason,
because the real error scrolls off the pane behind module-load warnings.

This is the defect behind "launch a claude-wrapped caret session" and the
`/launch` half of "left control panel works". It is **not** the EOF spin
(`seed_interpreter_stdin_read_line_erases_eof_2026-09-06.md`) — that one affects
the non-TTY path. This one affects the TTY path, and the two have opposite
symptoms: spin-forever vs die-in-2s.

## Bisect

A tmux pane IS a tty, so caret takes the TUI branch
(`src/app/llm_caret/tui_input.spl:31`:
`terminal_stdin_is_tty() and caret_term_supports_tui(env_get("TERM"))`).
Running the identical command in a tmux pane, varying only `TERM`, with stderr
redirected to a FILE so nothing scrolls away:

| case | `TERM` | result |
|---|---|---|
| TUI branch | `screen-256color` | **exited after 2s, exit=1** |
| plain branch | `dumb` | still alive after 40s — healthy |

The TUI case's stderr ends with exactly one error:

```
error: semantic: unknown extern function: rt_atexit_install
```

Repro: `scripts` in
`/tmp/.../scratchpad/panebisect.sh` (bisect harness kept out of the repo).

## Root cause

`rt_atexit_install` is **backed everywhere except the interpreter**:

| surface | status |
|---|---|
| `src/runtime/runtime.c:2732` | defined |
| `src/runtime/runtime_hosted_signal.c:44` | defined |
| `src/runtime/runtime_native.c:734` | defined (`SPL_CORE_C_WEAK`) |
| `src/runtime/runtime.h:1066` | declared |
| `src/compiler_rust/common/src/runtime_symbols.rs:1318` | registered |
| `src/compiler_rust/compiler/src/interpreter_extern/**` | **ABSENT (0 hits)** |

It is NOT in `scripts/check/unbacked_extern_baseline.txt`, because it is not an
unbacked extern in the link sense — the symbol genuinely exists. The gap is
specifically the seed **interpreter's** extern bridge.

Its siblings are all bridged: `interpreter_extern/terminal.rs` registers
`rt_stdin_read_byte`, `rt_terminal_enable_raw_mode`,
`rt_terminal_disable_raw_mode`, `rt_terminal_is_tty` and
`rt_terminal_get_size`. `src/lib/nogc_sync_mut/tui/terminal.spl:50` declares
`rt_atexit_install` and calls it at `:78` (`val exit_ok = rt_atexit_install() > 0`)
— it is the one extern in that module that was never bridged, so any TUI
entry through `terminal.spl` fails semantic resolution on the seed.

This is the class `scripts/check/check-interpreter-extern-registry-gap.shs`
exists to catch; that gate did not flag this one.

## Scope

Seed interpreter only. A NATIVE build links `rt_atexit_install` from
`runtime.c` and is expected to be unaffected — **unverified**, because no
self-hosted binary can be built on this host (the documented producer refuses on
a binary whose `--version` says `bootstrap seed only`, which is what
`bin/release/aarch64-unknown-linux-gnu/simple` says). So caret's TUI is
currently unreachable by the only runtime available here.

## Why it was not fixed in this change

The fix is a small addition to `interpreter_extern/terminal.rs` bridging
`rt_atexit_install` the way its siblings are bridged. That requires rebuilding
and redeploying the Rust seed — a heavy, shared-clone-hostile operation, and one
this repo has already been burned by: commit `e2d235c4739`
*"docs(sosix): revert the seed deploy and record why it was wrong"*. Other
sessions on this machine are actively using `bin/simple`, and swapping it
underneath them mid-session is exactly the failure that commit records.

Recorded rather than attempted. Whoever holds the seed-deploy lane should take
it together with the `Stdin.read_line` EOF erasure
(`seed_interpreter_stdin_read_line_erases_eof_2026-09-06.md`) — both are
one-function interpreter fixes in the same crate and should share a single
rebuild.

## Verify after fixing

```sh
tmux new-session -d -s t -x 200 -y 50 \
  'TERM=screen-256color bin/simple run src/app/llm_caret/main.spl 2>err.txt; echo $? >exit.txt'
# healthy = no exit.txt after 40s; broken = exit=1 and err.txt ends with
#   error: semantic: unknown extern function: rt_atexit_install
```

Consequence to re-check once green: `cs` `/launch caret` should then produce a
LIVE agent rather than one that immediately reads
`exited: pane pid <N> is not running`.
