# Lint directory targets fail as opaque files

## Status

Source-fixed; fresh pure-Simple Stage 4 qualification remains pending.

## Reproduction

The public CLI advertises directory linting, but the retained native CLI:

```sh
bin/simple lint test/fixtures/lint
```

returned nonzero with only `Lint failed in 1 file(s)`. It passed the directory
path directly to the single-file lint owner, did not inspect nested `.spl`
files, and emitted no target diagnostic. Missing files and parser errors
already failed correctly.

## Root cause and fix

`run_lint_command` collected positional targets and called `run_lint_file` for
each without distinguishing files from directories. It now expands directory
targets recursively through the hosted directory facade, keeps explicit files
unchanged, and fails with `no Simple source files found` when an explicit
directory contains no `.spl` files.

The focused CLI contract covers a relative directory with a clean root file and
a nested dirty file, plus an empty-source directory in JSON mode. The Stage 4
essential-tools gate also requires the recursive directory to emit W001, D001,
and the exact one-file failure summary.

A follow-up audit found that overlap deduplication compared display strings:
`./dir` plus `dir/file.spl` linted the same physical file twice. Shared source
discovery now supplies a canonical absolute identity while retaining the first
caller spelling for diagnostics. Both lint and check use that identity, and the
focused overlap contract deliberately mixes `./dir` with `dir/file.spl`.

## Evidence boundary

Source execution through the temporary Rust bootstrap interpreter produced one
W001 and one failed-file summary for the mixed-spelling overlap. This is not
production qualification: the retained binary predates the fix, and a fresh
Stage 4 essential-tools run remains required.
