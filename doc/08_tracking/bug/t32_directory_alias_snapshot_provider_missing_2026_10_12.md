# Directory alias provider omitted from admitted compiler snapshot

- **Status:** open — regression spec now executes; blocked on a POSIX host
- **Issue:** https://github.com/ormastes/simple/issues/3319
- **Code:** `src/app/compiler_entrypoint/inventory_events.spl`, `src/app/compiler_entrypoint/source_authority.spl`
- **Spec:** `test/02_integration/app/compiler_inventory_directory_alias_spec.spl`

## Summary

An admitted source snapshot lacked the logical `src/app/t32_cli` children even
though `src/app/t32_cli` is a tracked mode-120000 directory alias. An external
alias inventory repair was authored with a real-Git lifecycle regression that
had never been executed.

## 2026-11-03 (lane-a6dffc9c) — first execution of the regression

Run with the seed: `bin/simple.exe run test/02_integration/app/compiler_inventory_directory_alias_spec.spl`.

1. **Spec defect fixed:** the fixture created an empty `test/` directory and
   passed `test` as a `--source` root. Git tracks no empty directory, so the cold
   acquire failed with `source-inventory-root-empty: requested --source root
   'test' has no .spl/simple.sdn rows` before reaching any alias logic. The
   fixture now writes `test/probe.spl` and `git add`s `test`.
2. **Remaining blocker (Windows host only):** after (1) the cold acquire fails
   with `snapshot-source-owner-mismatch`
   (`src/app/compiler_entrypoint/source_authority.spl:189`). On this host the
   fixture's `ln -s` (MSYS, no `winsymlinks`) creates a directory COPY, not a
   symlink, so git records ordinary files instead of a mode-120000 alias — the
   spec's own docstring says "POSIX real-Git". The result is not evidence about
   the alias provider either way.

Repro on Linux/macOS: run the spec above; it must PASS (verdict
`passed=1`). If it fails with `snapshot-source-owner-mismatch` on POSIX, the
cache-root comparison at `source_authority.spl:189` is the defect.
