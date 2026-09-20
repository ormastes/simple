# `bin/simple stats` / `bin/simple doc-coverage` fail with "file not found" (seed dispatch gap)

## Symptom (RED, measured on deployed `bin/simple`, the Rust seed)
```
$ bin/simple stats
error: file not found: stats
$ echo $?
1
```
Same for `bin/simple doc-coverage`. Both print `error: file not found: <cmd>`,
then dump the top-level help.

**Correction to the original report:** exit code is already `1`, not `0`. The
"exits 0" observation was a pipe-measurement artifact
(`bin/simple stats 2>&1 | head -20; echo $?` reports `head`'s exit code, not
the compiler's). Verified directly with output redirected to a file instead
of a pipe: both commands exit `1`. So there is only one real sub-defect here,
not two.

## Root cause
`bin/simple` is currently the **Rust seed**
(`src/compiler_rust/target/bootstrap/simple`) — full self-host is blocked
(see `.claude/rules/bootstrap.md` "KNOWN BLOCKER"). The seed's command
dispatch table (`COMMAND_TABLE` in
`src/compiler_rust/driver/src/main.rs:408`) had **no entries at all** for
`"stats"` or `"doc-coverage"`. `real_main()` (main.rs:1163-1204) looks up the
first arg in `COMMAND_TABLE`; on a miss it falls through to
`handle_file_execution` (main.rs:1654), which treats the arg as a filename,
fails to resolve it, and prints `error: file not found: <cmd>` at
main.rs:1688 before returning exit code `1`.

The pure-Simple layer already implements both commands correctly:
- `src/app/cli/stats_entry.spl`
- `src/app/cli/doc_coverage_command.spl`
- both dispatched from `src/app/cli/_CliMain/main_and_help.spl:353` (`doc-coverage`) and `:425` (`stats`)
- both listed as `status: "implemented"` in `src/app/cli/surface_alignment.spl:45,96`

So this is purely a Rust-seed dispatch-table gap — the .spl implementation
was never wired into the seed's `COMMAND_TABLE`.

## Fix
Added two `CommandEntry` rows to `COMMAND_TABLE` in
`src/compiler_rust/driver/src/main.rs`, following the existing
`spipe-docgen`/`md-diagram-update` pattern (pure-Simple app, `Handler::Custom`
stub that only errors if the .spl app can't be launched at all):

```rust
CommandEntry {
    name: "doc-coverage",
    app_path: "src/app/cli/doc_coverage_command.spl",
    rust_handler: Handler::Custom(|_| {
        eprintln!("error: pure Simple doc-coverage app not found or failed to launch");
        1
    }),
    env_override: "",
    needs_rust_flags: &[],
},
CommandEntry {
    name: "stats",
    app_path: "src/app/cli/stats_entry.spl",
    rust_handler: Handler::Custom(|_| {
        eprintln!("error: pure Simple stats app not found or failed to launch");
        1
    }),
    env_override: "",
    needs_rust_flags: &[],
},
```

Also added `"doc-coverage"` and `"stats"` to `command_is_pure_simple_tool`
(main.rs:278) so dispatch always runs the .spl app and never falls back to
the Rust stub.

## Verification blocked by a second, unrelated pre-existing defect
Rebuilding the seed to test this fix (`CARGO_TARGET_DIR=/mnt/data/cargo-target-stats
cargo build --release -p simple-driver --bin simple`) fails during the
`simple-runtime` build script's C compile step:

```
src/runtime/runtime.h:1: error: version control conflict marker in file
    1 | <<<<<<< HEAD
src/runtime/runtime.h:1271: =======
src/runtime/runtime.h:2406: >>>>>>> a2bff98dd70 (fix(runtime): preserve u64 across erased values)
```

`src/runtime/runtime.h` has **literal, committed git conflict markers**
(confirmed via `grep -n '^<<<<<<<\|^=======\|^>>>>>>>' src/runtime/runtime.h`
→ hits at lines 1, 1271, 2406), landed by commit `57ed3ef0365` ("re-land the
extern-ABI campaign, clobbered a second time in one afternoon"). This is a
pre-existing, unrelated defect that blocks **every** Rust-seed build right
now, not just this change — `check-no-conflict-markers-push.shs` should have
caught it before landing but evidently didn't (or ran against a different
range). This needs its own fix (a real 3-way resolution of the extern-ABI
campaign content across the marker regions, ~2400 lines) — out of scope
here. Filing as a blocker so it isn't silently stepped over.

## Status
- `src/compiler_rust/driver/src/main.rs` dispatch-table fix: **written, not
  build-verified** (blocked by the runtime.h conflict-marker defect above).
  It is a small, mechanical, pattern-matched change (copy of the
  `spipe-docgen`/`md-diagram-update` entries) so risk is low, but it must be
  rebuilt and smoke-tested (`bin/simple stats`, `bin/simple doc-coverage`
  against the rebuilt binary) once `runtime.h` is repaired, before the next
  seed redeploy.
- No redeploy performed — per `.claude/rules/bootstrap.md`, full self-host is
  currently blocked anyway, and this fix only affects the seed binary, which
  users won't see until the next `--full-bootstrap --deploy`.
- Board-runnable: N/A — this is a CLI dispatch fix, not board/QEMU-related.

## RESOLVED — dispatch gap closed (verified 2026-08-17)

`bin/simple stats` and `bin/simple doc-coverage` no longer print
`error: file not found: <cmd>` + help. Both are recognized commands; on a host
without a deployed self-hosted binary they now say
`error: pure-Simple tool 'stats' unavailable; refusing Rust fallback`, which is
the intended seed behavior. The seed-command-table gap this doc reports is gone.

Spec coverage note (2026-08-17): no unit spec added — the defect is seed CLI
command-table dispatch (process-level `bin/simple stats` behavior), not a
library function; a unit spec cannot observe it without spawning the seed
binary, which the unit tree forbids. Verified manually instead (see above).
---

## RESOLVED 2026-08-17 — dispatch gap closed; residual is the known bootstrap blocker

Re-measured on the deployed `bin/simple` (still the Rust seed), output
redirected to a file, exit code read directly (not through a pipe):

```
$ bin/simple stats        -> rc=1
WARNING: this Rust-built Simple binary is a bootstrap seed only; ...
error: pure-Simple tool 'stats' unavailable; refusing Rust fallback

$ bin/simple doc-coverage -> rc=1
error: pure-Simple tool 'doc-coverage' unavailable; refusing Rust fallback
```

The reported defect was that `COMMAND_TABLE` had **no entries at all** for these
two commands, so `real_main()` fell through to `handle_file_execution` and
mis-reported them as `error: file not found: stats`. That is fixed:
`src/compiler_rust/driver/src/main.rs` now carries both names in the dispatch
table (`main.rs:318-319` in the recognised-command list, `main.rs:823` and
`main.rs:833` as table entries), and the commands are recognised — the message
is now an accurate statement of the real situation instead of a misleading
"file not found".

The remaining non-zero exit is **not this bug**: it is the seed correctly
refusing a Rust fallback for a pure-Simple-only tool, which is the documented
KNOWN BLOCKER in `.claude/rules/bootstrap.md`. Tracking of that belongs to the
bootstrap/self-host records, not here. Closing.
