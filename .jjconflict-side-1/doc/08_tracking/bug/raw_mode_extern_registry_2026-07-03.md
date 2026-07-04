# Fix: Calc TUI raw-mode keys — real root cause was the interpreter-fallback extern dispatch table, not module imports

**ID:** raw_mode_extern_registry_2026-07-03
**Date:** 2026-07-03
**Severity:** P3 — cosmetic in piped/scripted use (byte reads always worked
via the JIT/native path), but blocked real interactive per-keystroke
arrows/Enter in a real terminal, and threw "unknown extern function" for
`office edit-sheet --tui` specifically because that program's JIT compilation
falls back to the tree-walking interpreter for an unrelated reason.

## Summary

`bin/simple office edit-sheet --tui` (`src/app/office/mod.spl` /
`interactive.spl`) needs per-keystroke input (arrow keys as `ESC [ A/B/C/D`,
live Enter-commit) to drive `TuiState`/`tui_apply_key`. A prior session's
notes claimed:

> `rt_stdin_read_byte` resolves in bare entry scripts but is UNKNOWN when
> called from imported modules (extern registry gap) — the byte-reading loop
> was moved to `mod.spl` (the entry file) as a workaround.

**The "entry script vs. imported module" framing is disproven.** A probe
entry+module pair, structurally identical to `mod.spl` importing
`interactive.spl` (same-directory `use` import), ran fine through the
deployed self-hosted binary:

```
# probe_mod.spl
extern fn rt_stdin_read_byte() -> i64
fn read_one_byte() -> i64:
    rt_stdin_read_byte()

# probe_entry.spl
use probe_mod.{read_one_byte}
fn main() -> i64:
    val b = read_one_byte()
    print "byte={b}"
    0
```

```
$ printf 'A' | bin/simple run probe_entry.spl
byte=65
```

Also, `rt_terminal_enable_raw_mode`/`rt_terminal_disable_raw_mode` resolved
fine from an identically-shaped standalone module-import probe. So there is
no such thing as a "module extern registry" distinct from an "entry-script
extern registry" — `extern fn` declarations are resolved by name against the
same SFFI symbol table (`src/compiler_rust/common/src/runtime_symbols.rs`)
regardless of which module declares them, when the program JIT/AOT-compiles.

## Actual root cause (two independent gaps)

### Gap 1 — `rt_terminal_enable_raw_mode`/`rt_terminal_disable_raw_mode` were no-op stubs in the Rust runtime (JIT/AOT path)

`src/compiler_rust/runtime/src/value/sffi/env_process.rs:978-984` (before this
fix):

```rust
#[no_mangle]
pub extern "C" fn rt_terminal_enable_raw_mode() -> RuntimeValue {
    RuntimeValue::from_bool(true)
}
#[no_mangle]
pub extern "C" fn rt_terminal_disable_raw_mode() -> RuntimeValue {
    RuntimeValue::from_bool(true)
}
```

Never called `tcgetattr`/`tcsetattr` — so even with correct byte reads, a real
terminal never left canonical/echo mode.

### Gap 2 (the actual "unknown extern function" crash) — the interpreter-fallback dispatch table never had these four `rt_` names at all

`bin/simple office edit-sheet --tui` fails to fully JIT-compile for an
**unrelated** reason (`[INFO] JIT compilation failed, falling back to
interpreter: HIR lowering error: Unknown variable: Option while lowering
UndoStack.undo` — a separate pre-existing bug, out of scope here), so the
whole program runs through the tree-walking interpreter instead of
JIT/AOT-compiled native code. In that fallback mode, every `extern fn` call is
dispatched by exact string match against a ~1400-entry table built in
`init_dispatch_table()`
(`src/compiler_rust/compiler/src/interpreter_extern/mod.rs`). That table had
`rt_stdin_read_line` and `rt_time_now_unix_micros` registered (which is why
those "worked"), but **no entry at all** for `rt_stdin_read_byte`,
`rt_terminal_enable_raw_mode`, `rt_terminal_disable_raw_mode`, or
`rt_terminal_get_size` — hence `error: semantic: unknown extern function:
rt_terminal_enable_raw_mode` when actually running the real
`office edit-sheet --tui` command (reproduced with the pre-fix source; the
isolated probes above never trip the unrelated JIT-fail path, so they always
"worked").

Notably, real (non-stub) raw-mode termios logic for the interpreter path
*already existed* under different names:
`terminal::native_enable_raw_mode`/`native_disable_raw_mode`/
`native_get_term_size` in
`src/compiler_rust/compiler/src/interpreter_extern/terminal.rs`, backed by
`src/compiler_rust/compiler/src/interpreter_native_io.rs:394-490` (a full
`tcgetattr`/`tcsetattr` implementation with `ORIGINAL_TERMIOS` thread-local
save/restore). These are a legacy pre-`rt_`-prefix naming convention,
registered under `"native_enable_raw_mode"` etc.
(`interpreter_extern/mod.rs:286-308`) and take a numeric fd-handle arg /
return an `i64` status code — a different signature than the `rt_`-prefixed
externs `terminal.spl` actually declares (`() -> bool`, `() -> (i64, i64)`).

## Fix

1. `src/compiler_rust/runtime/src/value/sffi/env_process.rs` — implemented
   `rt_terminal_enable_raw_mode`/`rt_terminal_disable_raw_mode` for
   `cfg(unix)` using `nix::sys::termios` (`term` feature already enabled,
   `Cargo.toml:117`; same crate already used the same way in
   `src/compiler_rust/runtime/src/value/serial.rs`): `tcgetattr` → save into
   `OnceLock<Mutex<Option<Termios>>>` → `cfmakeraw()` → `tcsetattr(TCSANOW)`;
   disable restores the saved termios. Non-unix keeps the old `true` stub.

2. `src/compiler_rust/compiler/src/interpreter_extern/terminal.rs` — added
   four adapter functions with the exact `rt_` names/signatures, bridging to
   the existing `native_*` implementations:
   `rt_stdin_read_byte` (direct 1-byte `std::io::stdin().read`),
   `rt_terminal_enable_raw_mode`/`rt_terminal_disable_raw_mode` (call
   `native_enable_raw_mode`/`native_disable_raw_mode` with handle `0` /
   stdin, map `Int(0)` → `Bool(true)`), `rt_terminal_get_size` (calls
   `native_get_term_size` with handle `1` / stdout, swaps its `[rows, cols]`
   to the `(cols, rows)` tuple order `terminal.spl`'s `terminal_get_size()`
   expects).

3. `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` — registered
   the four new adapters in `init_dispatch_table()` next to the existing
   `native_*` entries.

4. `src/app/office/interactive.spl` — added `run_sheet_tui_mode(in_path)`: a
   byte-at-a-time loop (`rt_stdin_read_byte`) wrapped in
   `rt_terminal_enable_raw_mode()`/`rt_terminal_disable_raw_mode()`, reusing
   the existing pure `tui_new_state`/`tui_apply_key`/`tui_frame` state
   machine. `src/app/office/mod.spl`'s `_run_sheet_tui` now just calls it
   instead of duplicating a line-based byte-feeding fallback loop in the
   entry file.

## Verification

- `cargo check -p simple-runtime` — clean.
- `cargo check -p simple-compiler` — clean (only 2 pre-existing unrelated
  warnings).
- Probe: `rt_stdin_read_byte` and `rt_terminal_enable_raw_mode` both resolve
  and execute correctly from an imported module via the JIT/native path
  (`byte=65` for piped `A`; raw-mode probe returned a bool without error) —
  proves gap 1's dispatch path is fine outside the interpreter fallback.
- `cd src/compiler_rust && cargo build --profile bootstrap -p simple-driver
  -p simple-native-all` — rebuilt the seed + native-all lib twice (once for
  the runtime fix, once more after adding the interpreter_extern adapters);
  both completed successfully (~4 min each).
- **End-to-end acceptance against the rebuilt seed**
  (`SIMPLE_BOOTSTRAP=1 src/compiler_rust/target/bootstrap/simple run
  src/app/office/mod.spl edit-sheet tui_test.csv --tui` with piped bytes
  `ESC [ C 5 \n q`): right-arrow moved the active cell A1→B1, `5`+Enter
  committed (`B1 = 5` shown in the redrawn grid and status bar — live
  recalc), `q` quit with `bye`. No "unknown extern function" error — the
  same command reproduced `error: semantic: unknown extern function:
  rt_terminal_enable_raw_mode` before the fix.
- Module-context probes via the rebuilt seed interpreter:
  `printf 'A' | ... run probe_entry.spl` → `byte=65`
  (`rt_stdin_read_byte` resolving from an imported module), and the
  raw-mode entry+module probe pair ran without an unknown-extern error
  (enable correctly reports failure when stdin is not a tty).
- NOT yet shipped into the deployed self-hosted binary: the full stage2-4
  rebuild + `--deploy` swap of `bin/release/<triple>/simple` was deliberately
  not run in this session — it is a long job, and swapping the shared binary
  mid-flight is hazardous with parallel agent sessions active. Run
  `scripts/bootstrap/bootstrap-from-scratch.sh --pure-simple --deploy` (the
  seed at `src/compiler_rust/target/bootstrap/simple` already contains all
  fixes) when the tree is quiet. Raw-mode `tcsetattr` behavior can only be
  observed at a real tty (not piped stdin), so final interactive verification
  also needs a pty harness (`script`, `tmux`, or pexpect-style).

## Fix Options (if further work needed)

1. If the self-hosted deploy did not land in this session, rerun
   `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` (or the manual
   stage2 `native-build` from `.claude/rules/bootstrap.md`) to ship all four
   fixes into `bin/release/<triple>/simple`, then smoke-test with a real pty.
2. Fix the unrelated `UndoStack.undo` HIR lowering bug ("Unknown variable:
   Option") so `office edit-sheet --tui` JIT-compiles cleanly instead of
   silently falling back to the interpreter — the interpreter fallback is a
   legitimate safety net, but every extern a JIT-fail-prone program might call
   needs a fallback-table entry too, which is easy to miss (as this bug shows).
   Consider a lint/test that diffs `runtime_symbols.rs`'s master extern list
   against `interpreter_extern::mod.rs`'s dispatch table and flags `rt_`-named
   externs present in the former but absent from the latter.
3. `cfmakeraw()` (used in the Gap 1 fix) clears `ISIG`, so Ctrl-C will not
   raise SIGINT while the Calc TUI is in raw mode; `q` is the documented quit
   key. If that surprises users, restore `ISIG` after `cfmakeraw()` and before
   `tcsetattr`. (The interpreter-path `native_enable_raw_mode`, gap 2, already
   made this same ISIG-disabling choice explicitly.)
