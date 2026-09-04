# `simple stats` prints the file counts and then hangs indefinitely

- Date: 2026-09-02
- Status: OPEN
- Severity: medium (the command never completes; no verdict, no exit)
- Binary: `bin/simple.exe`, md5 `d52d770724a9f8797e98ac7819709ab9`, 16,347,136 bytes, mtime 2026-09-01 17:54
- Platform observed: Windows 11 (x86_64-pc-windows-msvc)

## Measured

```
$ bin/simple.exe stats
=========================================
Simple Project Statistics
=========================================

Collecting data...

Files:
  Total:      16220 source files
    app:        3138 files
    lib:        8028 files
    std:        29 files
    core:       0 files
    compiler:   5025 files
  Tests:      25072 test files
```

...and nothing further. Started 15:23; the log file's last write was 15:23 and it
was still unchanged at 16:04 — **41 minutes with zero further output** and no
exit. The process was never observed to terminate on its own.

Contrast: `bin/simple.exe todo-scan`, which walks a LARGER set (71,679 files),
completes cleanly in the same tree — `Scan complete: 265 TODOs found`, rc=0. So
this is not simply "the repo is big".

The counts that DO print are correct and are useful evidence in their own right
(they are the numbers that show `doc-coverage`'s "No source files found" was a
lie — see `doc_coverage_sdoctest_functions_never_implemented_2026-09-02.md`).

## Where it stops

Output stops immediately after the `Tests:` line and before any doc-coverage
section. `simple stats` is documented as including doc coverage
(`.claude/rules/commands.md`: "`bin/simple stats` — Doc coverage in stats"), and
the doc-coverage code path is independently known-broken in this tree, so the
first thing to check is whether `stats` blocks inside the same
`src/app/doc_coverage/**` code — in particular whether it, too, is stuck behind
an `is_dir` guard that never returns true (see
`is_dir_returns_false_for_every_path_in_interpreted_module_2026-09-02.md`).

That is a HYPOTHESIS, not a finding: no profiling was attempted, and the
interpreter sampling env vars are documented as emitting nothing from a deployed
seed of this vintage.

## Next steps

1. Locate the stats implementation's section boundary and add a level-gated
   progress log at each section start, so the stalling section is named rather
   than inferred.
2. Re-run after `doc-coverage` is repaired; if the hang disappears, this record
   closes as a duplicate of that one.
