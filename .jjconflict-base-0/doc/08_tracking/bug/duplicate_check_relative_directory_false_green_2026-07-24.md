# Duplicate-check relative directory false-green

## Status

Source-fixed; fresh pure-Simple Stage 4 qualification remains pending.

## Reproduction

From the repository root, the retained native CLI returned success for:

```sh
bin/simple duplicate-check test/fixtures/duplication/clean_pair \
  --no-default-excludes --mode token --min-lines 5 --min-tokens 8 --format json
```

Its output said `Scanning 0 files` and reported zero duplicate groups. The
target exists and contains two `.spl` files, so the clean result was vacuous.
The bootstrap essential-tools gate did not expose the bug because every
duplicate-check directory argument was absolute.

## Root cause and fix

The native `rt_dir_walk` path used by `collect_detector_files` does not resolve
relative directories. The shared collector now uses `rt_path_absolute` only
for the native directory walk, then restores each result to the caller's
original relative-root spelling before exclusion, reporting, and cache lookup.
Single-file identity is unchanged.

The known-duplicate bootstrap probe now passes `duplicates` relative to its
temporary external working directory and excludes a nested copied pair with
`duplicates/ignored/**`. Its existing assertions require one group, two
occurrences, and ten lines, preventing both zero-file success and rooted
relative-exclude regressions.
The Rust-bootstrap workflow path filters now include the essential gate and
its direct fixtures/system contract so gate-only changes trigger CI.

## Evidence

- Retained native CLI before fix: exit 0, `Scanning 0 files`.
- Current-source temporary bootstrap run: exit 0, `Scanning 2 files`, zero
  groups for `clean_pair`.
- Focused pure-Simple native entry-closure build was stopped after 120 seconds
  with no output or artifact. It is not qualification evidence.

Run the exact fresh Stage 4 essential-tools gate once an admitted candidate is
available; do not accept the temporary bootstrap result as release evidence.
