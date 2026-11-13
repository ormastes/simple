# rt_terminal_disable_raw_mode panics "RefCell already borrowed" (SIGABRT on every raw-mode quit)
## Closed 2026-09-16 — ...s first), then the process aborts. ## Fix (one-liner shape) Copy the saved termios out and

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

- Date: 2026-07-04
- Status: OPEN (diagnosed, one-line fix identified, seed rebuild required)
- Severity: high — every keystroke-driven TUI/GUI session that quits cleanly
  from a real terminal crashes with exit 134 instead of restoring the
  terminal and printing "bye"
- Affects: `office edit-sheet --tui` (run_sheet_tui_mode),
  `office sheet-gui-live` (run_sheet_gui_live),
  `office slides-gui-live` (run_slides_gui_live) — anything that calls
  `rt_terminal_disable_raw_mode()` after a successful
  `rt_terminal_enable_raw_mode()` under the interpreter path.

## Repro (real pty; the non-TTY pipe path never reaches disable, so it does not crash)

```bash
( sleep 55; printf 'n'; sleep 4; printf '\033[C'; sleep 4; printf 'q'; sleep 6 ) | \
  timeout 180 script -qec \
  "src/compiler_rust/target/bootstrap/simple run src/app/office/mod.spl office slides-gui-live" \
  /tmp/pty.typescript
# navigation works (n -> slide 2/3, right-arrow -> 3/3), then 'q' quits the
# loop and rt_terminal_disable_raw_mode() aborts:
#   Message: RefCell already borrowed
#   Location: compiler/src/interpreter/../interpreter_native_io.rs:455:19
#   10: simple_compiler::interpreter::interpreter_native_io::native_disable_raw_mode
# COMMAND_EXIT_CODE="134", crash log .simple/logs/crash_*.log
```

Verified 2026-07-04 against the rebuilt seed
`src/compiler_rust/target/bootstrap/simple` (the one carrying the
raw_mode_extern_registry_2026-07-03.md fixes; the deployed
`bin/release/x86_64-unknown-linux-gnu/simple` still lacks the raw-mode
externs entirely — `error: semantic: unknown extern function:
rt_terminal_enable_raw_mode` — so it fails earlier for a different,
already-tracked reason).

## Root cause

`src/compiler_rust/compiler/src/interpreter_native_io.rs`,
`native_disable_raw_mode` (unix):

```rust
ORIGINAL_TERMIOS.with(|orig| {
    if let Some(termios) = *orig.borrow() {          // immutable borrow HELD
        unsafe {                                     // for the whole if-let
            if libc::tcsetattr(fd, libc::TCSAFLUSH, &termios) != 0 {
                return Ok(Value::Int(-1));
            }
        }
        *orig.borrow_mut() = None;                   // second borrow -> panic
    }
    Ok(Value::Int(0))
})
```

The temporary from `orig.borrow()` lives until the end of the `if let`
statement (pre-2024-edition temporary lifetime rules), so the
`borrow_mut()` inside the body is a guaranteed `BorrowMutError` whenever a
saved termios exists — i.e. exactly when raw mode was successfully enabled
and there is something to restore. The terminal IS restored (tcsetattr runs
first), then the process aborts.

## Fix (one-liner shape)

Copy the saved termios out and end the borrow before mutating:

```rust
let saved = *orig.borrow();          // libc::termios is Copy
if let Some(termios) = saved {
    unsafe {
        if libc::tcsetattr(fd, libc::TCSAFLUSH, &termios) != 0 {
            return Ok(Value::Int(-1));
        }
    }
    *orig.borrow_mut() = None;
}
Ok(Value::Int(0))
```

Then rebuild the seed and redeploy the self-hosted binary (same pending
deploy as raw_mode_extern_registry_2026-07-03.md — both fixes ship in the
same `bootstrap-from-scratch.sh --pure-simple --deploy` pass when the tree
is quiet).

## Scope notes

- Pure-Simple callers are correct as written: run_sheet_tui_mode,
  run_sheet_gui_live, and run_slides_gui_live all call
  disable-after-enable exactly once on the quit path; no .spl change needed.
- The `office slides-gui-live` / `sheet-gui-live` non-TTY safety path
  (piped stdin: one frame + notice + exit 0) is unaffected — enable fails
  on a pipe, so disable is never reached.



---

## Lane disposition 2026-11-13 (p3-misc-b)

diagnosed with a one-line fix identified, but the fix is in the Rust seed runtime (rt_terminal_disable_raw_mode) and requires a seed rebuild - not available on this Windows lane. Owner: seed lane.
---

## Addendum 2026-11-13 — lane live-p3-l4 (work/live-p3-l4-20261113, base f790f7f266e) — VERIFIED FIXED in source and in the deployed build; no code change

The one-line fix this record specifies is present verbatim at
`src/compiler_rust/compiler/src/interpreter_native_io.rs:448-464`
(`let saved = *orig.borrow();` copied out before the `borrow_mut()`, with a
comment naming this record's abort) on the `#[cfg(unix)]` arm of
`native_disable_raw_mode`. `git log -S "round-8 raw-mode-quit abort"` dates
it to ae55a746719 (2026-08-11 tree restore), and
`git merge-base --is-ancestor` confirms that commit IS an ancestor of the
deployed Windows seed's build-commit 0791c2b7f4a7 (refresh #8184) — so the
deployed binary carries the fix. The header Status line was never flipped;
that bookkeeping is the only open part.

Runtime re-verification is not possible on this Windows lane: both raw-mode
entry points are `#[cfg(unix)]` (on Windows `native_enable_raw_mode`
returns -2 and `native_disable_raw_mode` returns 0 without touching
termios), and the repro requires a real Unix pty. Source review of the
enable path (`:395-421`) shows no analogous held-borrow shape. If the
symptom recurs on a Unix host, re-open with a fresh dated pty repro per the
header instruction.
