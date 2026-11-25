# Bug: `bin/simple build lint <file>` triggers a full cargo/clippy driver rebuild
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- **ID:** build_lint_subcommand_triggers_full_driver_rebuild_2026-06-15
- **Filed:** 2026-06-15
- **Severity:** P3 (tooling UX / latency)
- **Area:** build CLI / `build lint` subcommand
- **Found by:** bytes-foundation feature

## Summary

Running `bin/simple build lint src/lib/common/bytes/span.spl` did not lint the
Simple file. Instead it ran a full Rust `cargo`/`clippy` rebuild of
`simple-driver` (output was clippy warnings about `simple-driver` lib code,
"Finished `dev` profile ... in 54.15s"), then timed out before producing any
Simple-level lint result for the target file.

## Workaround

Invoke the seed driver's `lint` directly:

```bash
export SIMPLE_BOOTSTRAP_DRIVER=$(ls -1 bin/release/*/simple_seed | head -1)
"$SIMPLE_BOOTSTRAP_DRIVER" lint src/lib/common/bytes/span.spl
```

This returns Simple-level lint diagnostics in <1s (e.g. it correctly flagged
`export_outside_init` warnings on the new files, which guided moving exports to
`__init__.spl`).

## Expected

`bin/simple build lint <file>` should lint the given Simple file using the
already-built driver (or the seed driver) without re-invoking cargo/clippy on
the Rust crates. A per-file lint should be sub-second, not a 50s+ crate rebuild.

## Notes

- AC-9 lint evidence for the bytes-foundation feature was therefore gathered via
  the seed driver path above (all 6 files report CLEAN).
- Related but distinct from
  `rust_driver_rebuild_blocks_short_grammar_interpolation_verification_2026-05-27`
  (that was a build-script symbol-scan issue, now resolved); this is the
  `build lint` subcommand falling through to a cargo rebuild.

## Triage 2026-09-13 — LEFT OPEN (still reproduces)

- **measured** (Rust seed `bin/simple` v1.0.0-rc.1, Windows): `bin/simple build lint src/lib/common/bytes/span.spl` still goes into cargo instead of linting the Simple file. It printed `Blocking waiting for file lock on build directory` and was killed at the 120 s bound (rc=124) having produced zero Simple-level lint output.
- **inferred**: the cargo lock contention is incidental — a bootstrap was running concurrently on this host — but it is only reachable because `build lint` enters the Rust build at all, which is the defect. The `<file>` argument is still not routed to the Simple linter.
- **inferred**: the entry's workaround (invoke the seed driver's `lint` directly) remains the way to get Simple-level diagnostics; `.claude/rules/commands.md` documents `bin/simple lint <files>` as the sanctioned pure-Simple path, so `build lint` arguably should reject a `.spl` argument rather than silently rebuilding the driver.
- Verdict: OPEN — P3 tooling UX, unchanged since filing.


## Resolution 2026-11-25 — root cause isolated to the Rust seed; pure-Simple CLI already routes correctly

### Root cause (two layers, both in the Rust seed)

1. **Simple-first dispatch for `build` is dead.** The seed's command table
   entry for `build` (`src/compiler_rust/driver/src/main.rs:486-492`) names
   `app_path: "src/compiler/80.driver/build/cli_entry.spl"`, but that file no
   longer exists — the build CLI moved to `src/app/build/cli_entry.spl`. More
   decisively, `dispatch_to_simple_app` (main.rs:1466-1531) returns `None` for
   any app path outside its hardcoded allowlist *before* touching the
   filesystem, and the build entry path is not in that allowlist. So `build`
   always falls through to the Rust fallback handler.
2. **The Rust fallback hijacks `lint`.** `handle_build`
   (`src/compiler_rust/driver/src/cli/commands/misc_commands.rs:130`) matches
   `"lint"` and calls `handle_build_lint_with_args` (misc_commands.rs:185),
   which runs `cargo clippy --manifest-path src/compiler_rust/Cargo.toml
   --workspace` and ignores every trailing argument, including `.spl` files.
   That is the 50s+ driver rebuild this bug recorded.

### Pure-Simple current source is already correct

On the self-hosted CLI, `simple build lint <file.spl>` dispatches
`_CliMain/main_and_help.spl:698` -> `app.build.cli_entry.handle_build`, where
`src/app/build/cli_entry.spl:179-180` routes `lint` to `cli_run_lint(args[1:])`
(`src/app/io/_CliCommands/run_commands.spl:243`), which lints each file via
`run_lint_file` — the same sanctioned path as `simple lint <file>`. The
routing fix preferred by the 2026-09-13 triage note is already in place; no
pure-Simple change is required.

### Verification evidence (2026-11-25, Windows worktree C:\wt-p3-buildlint)

- **Reproduced on the deployed seed** (v1.0.0-rc.1):
  `./bin/simple.exe build lint src/lib/common/bytes/span.spl` immediately
  entered cargo (`error: patch location ... libmimalloc-sys ...`, failing fast
  only because this sparse worktree lacks the vendored patch crate) and
  produced zero Simple-level lint output — the `.spl` argument never reaches
  the Simple linter. In a full checkout this is the recorded 50s+ clippy
  rebuild.
- **Interpreter verification of current source is environment-blocked on this
  host**: every available binary (`bin/simple` beta.11,
  `src/compiler_rust/target/bootstrap/simple.exe` rc.1) predates the current
  `unit Name: i64` grammar, so
  `SIMPLE_LIB=src ./bin/simple.exe run src/app/cli/main.spl -- build lint src/lib/common/bytes/span.spl`
  fails at parse in `src/lib/common/types.spl`
  (`Unexpected token: expected As, found Newline`) before any dispatch runs.
  The pure-Simple routing was therefore verified by code inspection of the
  call chain above, not by execution.
- No unit spec under `test/01_unit` covers `app/build/cli_entry.spl`
  dispatch; the only specs referencing `build lint`
  (`test/02_integration/app/app_cli_intensive_spec.spl`) cannot run for the
  same parser-vintage reason.

### Remaining work (Rust seed only — out of scope for pure-Simple)

Per repo policy the Rust seed is bootstrap-only and the self-hosted binary is
the default tool, so the residual defect is fixed in `src/compiler_rust` or
not at all. Either:

- point the `build` CommandEntry at `src/app/build/cli_entry.spl` and add that
  path to the `dispatch_to_simple_app` allowlist (main.rs), so the seed
  delegates `build` to Simple the way it already delegates `lint`/`fmt`; or
- make `handle_build_lint_with_args` reject `.spl` arguments with a pointer to
  `simple lint <file>` instead of silently running cargo clippy.

- Verdict: CLOSED for the pure-Simple CLI (routing already correct on
  release/1.0.0); the seed-side remnant is Rust-only and tracked by the
  recommendation above.
