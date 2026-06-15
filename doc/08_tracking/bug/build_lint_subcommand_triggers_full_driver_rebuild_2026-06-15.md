# Bug: `bin/simple build lint <file>` triggers a full cargo/clippy driver rebuild

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
