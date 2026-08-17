# Bug: `bin/simple build lint <file>` triggers a full cargo/clippy driver rebuild

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

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

## 2026-08-17 verification (CLI lane) — STILL OPEN; SAME ROOT CAUSE as
## build_lint_routes_to_rust_clippy_not_cli_run_lint_2026-07-06.md

These two rows are one defect, not two. `bin/simple build lint <file>` reaches
`src/compiler_rust/driver/src/cli/commands/misc_commands.rs:130` ->
`handle_build_lint_with_args`, which discards the file argument and shells out
to `cargo clippy --manifest-path src/compiler_rust/Cargo.toml --workspace`.
The full-workspace cargo/clippy rebuild reported here IS that `cargo clippy`
invocation; it is not a separate build-system defect. Fixing the routing (see
the sibling doc) removes the rebuild by construction, because the pure-Simple
linter never invokes cargo.

Not patched by this lane (Rust file, out of scope). Verified by content, not
by SHA.
