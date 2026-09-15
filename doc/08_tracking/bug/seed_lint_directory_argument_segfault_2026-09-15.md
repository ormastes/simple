# Seed `lint` segfaults on a directory argument

- **Observed (2026-09-15, seed `bin/release/aarch64-unknown-linux-gnu/simple`,
  50,093,192 bytes, mtime 2026-09-06):** `bin/simple lint <dir>` segfaults
  (rc=139, core dumped). Reproducer:
  `SIMPLE_TIMEOUT_SECONDS=120 timeout 120 bin/simple lint test/01_unit/compiler/deep`
  → `Segmentation fault`, no diagnostics. The single-FILE lane is fine on the
  same binary (`bin/simple lint src/lib/common/base_encoding.spl` → rc=0,
  "Lint passed"), so the defect is in the directory-enumeration/multi-file path,
  not the linter core.
- **Impact:** no lint verification of directory-scoped changes on this host;
  the aarch64 seed is the only runnable binary here (phase-3 binaries are
  x86_64). Found during the 2026-09-15 full-suite wave; earlier notes
  over-broadly recorded "lint core-dumps on every input".
- **Suspect:** directory argument handling in the lint entry
  (`src/app/cli/lint_entry.spl` / `app.io.cli_lint_commands`) or its Rust-side
  seed twin — whatever expands a dir into a file list.
- **Unblock condition:** `bin/simple lint <dir>` returns a verdict (or a clean
  usage error) instead of SIGSEGV; re-verify with the reproducer above on both
  seed and self-hosted binaries.
