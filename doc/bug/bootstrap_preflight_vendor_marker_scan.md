# Bootstrap preflight reads excluded vendor dependencies

## Evidence

On Windows during the 2026-10-21 `release_phase3` bootstrap from
`380200890ff`, preflight's marker grep (PID 33496) accumulated approximately
474 CPU seconds. `paired_markers` recursively read all `src/compiler_rust`,
including `vendor`, before its caller removed `/vendor/` matches.
This excluded dependency content from the verdict but retained the I/O cost.

## Repair

Use `find` to prune directories named `vendor` before passing owned regular
files to batched grep. Keep both marker predicates on the same file, preserve
quoted paths, and remove the now-redundant caller-side filter. A directory
named `vendor-owned` remains owned and must still be checked.

## Verification

The preflight `--selftest` fixtures cover owned paired markers, clean content,
unpaired markers in the same and separate files, paired vendor content,
vendor as the scan root, and owned file/directory names containing spaces.
This is a traversal-scope repair; no full-bootstrap speedup is claimed without
a comparable full run. The running parent bootstrap source remains unchanged.
