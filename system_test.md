# System Tests

## Tooling
- Prefer the driver stack for end-to-end coverage (`Runner` in `src/driver`) and `shadow-terminal` for headless CLI runs.
- Add `shadow-terminal` to the crate hosting CLI tests (driver) to script key presses, await output, and assert exit codes/buffers without a real TTY.
- Keep system tests fast: use tempdirs, avoid network, and assert only what matters (exit code, emitted SMF, visible diagnostics).

## CLI test #1 (happy path: compile + run)
- Create a temp workspace with `main.spl` (exercise dependency analysis + SMF emission).
- Run the CLI via `shadow-terminal`: `cargo run -p driver -- run <path> [--gc-log]`.
- Assert: exit code `0`, `.smf` exists/non-empty next to the source, stdout contains a success banner (e.g., `Built main.smf` or a GC log marker when `--gc-log` is passed).
- Capture the final screen buffer to ensure diagnostics are readable (no wrapped lines/ANSI glitches).

```rust
#[test]
fn cli_happy_path() -> shadow_terminal::Result<()> {
    let tmp = tempfile::tempdir()?;
    let src = tmp.path().join("main.spl");
    std::fs::write(&src, "main = 0")?;

    let mut term = shadow_terminal::Command::new([
        "cargo", "run", "-p", "driver", "--", "run",
        src.to_str().unwrap(), "--gc-log",
    ])
    .rows(24)
    .cols(80)
    .spawn()?;

    term.wait_for_stdout("gc:start reason=post-run")?;
    term.wait_for_exit_success()?;
    assert!(src.with_extension("smf").exists());
    Ok(())
}
```

## Existing coverage to extend
- `src/driver/tests/runner_tests.rs`: runner compiles/runs inline source, runs from file, checks dependency analysis, and asserts GC logging hooks.
- `src/driver/tests/watcher_tests.rs`: watcher rebuilds on file change and emits the refreshed `.smf`.

## Next scenarios to automate
- **CLI watch mode**: start `watch <src>` under `shadow-terminal`, mutate the source, assert a rebuild message and `.smf` mtime bump, then kill the session cleanly.
- **Diagnostics**: feed invalid source, expect non-zero exit and a plain-text error snippet (no ANSI dependency).
- **Dependency invalidation**: `main.spl` imports `util.spl`; touching `util.spl` should bump `main.smf` after the watcher rebuilds.
- **Macro tracking**: define `macro FOO(x) = x`; change the body; dependents should rebuild (matches `dependency_cache` behavior).
- **GC logging (verbose)**: use `Runner::with_gc(GcRuntime::with_logger(...))` or CLI `--gc-log` to assert `gc:start/gc:end` markers are emitted around post-run collection.

## GC/Abfall hooks
- Runtime GC (`simple_runtime::gc::GcRuntime`) wraps Abfall in `src/runtime/gc`, emitting structured `GcLogEvent` markers.
- In system tests, prefer `Runner::with_gc(GcRuntime::with_logger(...))` for in-memory assertions; use `Runner::new_with_gc_logging()` or `--gc-log` to surface logs to stdout for CLI-oriented cases.
