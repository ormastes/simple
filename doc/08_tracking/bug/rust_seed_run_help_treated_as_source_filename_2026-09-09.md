# Rust seed `run --help` is treated as a source filename

- **ID:** `rust_seed_run_help_treated_as_source_filename_2026-09-09`
- **Date:** 2026-09-09
- **Status:** OPEN
- **Severity:** P2
- **Component:** `src/compiler_rust/driver/src/main.rs`

## Symptom

On the deployed Windows Rust seed, `simple run --help` enters source-file
handling and reports a missing file for `--help` instead of printing run usage.
This is narrower than the deployment-authority defect: even a deliberately
invoked seed should parse a subcommand-local help flag as help, not a filename.

## Impact and oracle

The run help smoke is red and command discovery is misleading. It does not by
itself prove that direct execution of a real `.spl` file is broken. A fixed
binary must make `simple run --help` exit zero, print run usage, and perform no
source-file open for a path named `--help`.

## Re-check 2026-09-13

- Status: OPEN (P2) — reproduces identically on Linux, not Windows-specific

```
$ bin/simple run --help
error: compile failed: io: Cannot read "--help": No such file or directory (os error 2)
```

Binary: `bin/simple` = Rust seed `bin/release/aarch64-unknown-linux-gnu/simple`
(symlinked from the shared main worktree), sha256 `3d120a6f9ab5`,
`Simple Language v1.0.0-rc.1`. Confirms the defect is in the shared
`src/compiler_rust/driver/src/main.rs` CLI arg parsing, not a
Windows-platform-specific path. Rust seed source, out of scope for a
pure-Simple lane fix; left OPEN, no code change attempted.

## Relationship

The currently deployed binary is independently disqualified by
`deployed_bin_simple_still_seed_2026-08-05.md`. Keep this parsing symptom
separate so a correct Stage 4 deployment does not silently hide the seed CLI
contract defect.
