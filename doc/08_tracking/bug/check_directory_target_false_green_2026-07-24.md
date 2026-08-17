# Check directory target false-green

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Symptom

`simple check <empty-directory>` printed `OK` without checking a Simple source.
Directory targets with sources were also passed to the parser as one opaque
path instead of being expanded recursively.

## Root cause

The check entry and worker treated every positional target as a file. Unlike
lint, neither layer expanded directories before dispatch. Native
`rt_dir_walk` also requires an absolute scan root for reliable relative-path
use.

## Fix

Check now expands directories through the same native-safe source discovery
used by lint. It restores caller-relative spelling, sorts and deduplicates
discovered `.spl` files, rejects explicit empty directories, and reports counts
for actual checked files. Existing per-file worker isolation remains intact.

## Regression evidence

`test/03_system/app/check_cli_directory_contract_spec.spl` covers:

- recursive relative-directory checking;
- overlapping directory/file deduplication;
- repeated empty-directory fail-closed behavior.

The retained deployed CLI reproduced the old worker false-green on 2026-07-24.
Fresh pure-Simple Stage 4 runtime qualification remains pending.

## Fresh runtime qualification 2026-08-17 — NOT REPRODUCED, closing

The "fresh pure-Simple Stage 4 runtime qualification remains pending" gate
above is now satisfied against the deployed `bin/simple`. Classified by
CONTENT, not by commit ancestry (SHA ancestry is unsound in this repo).

Source evidence: `src/app/check/main.spl:293` destructures
`expand_check_targets(raw_files)` into `(files, empty_directories)`.
`src/app/check/targets.spl` tests `rt_dir_exists(target)`, expands a real
directory via `discover_spl_files`, and pushes a directory that yields zero
sources onto `empty_directories`. Back in `main.spl:295`, `errors` is
*initialised* to `empty_directories.len()`, so an empty directory target is
counted as an error before any file is checked, and `main.spl:317` returns 1
whenever `errors != 0`.

Runtime evidence, two fixtures, exit code assigned on the line after the
command and never read through a pipe:

1. Directory containing one deliberately broken source:

       $ bin/simple check .../srcdir
       3 error(s) found in 1 of 1 file(s)
       rc=1

   The directory's contents were discovered and actually checked — this is the
   precise behaviour whose absence the bug alleges.

2. Directory containing no Simple sources at all:

       $ bin/simple check .../emptydir
       rc=1

   Fails closed rather than reporting green on a vacuous target.

Neither the directory-not-expanded false green nor the empty-directory false
green reproduces.

Status: NOT REPRODUCED / already fixed in source. No code change made.

## Verification 2026-08-17 (wave_00 w0001/app_1) — CLOSE by content

Directory targets are now expanded and an EMPTY directory is a hard error.

`src/app/check/targets.spl:22-30`:

```
        if not rt_dir_exists(target):
            ...
            continue
        val discovered = discover_spl_files(target)
        if discovered.len() == 0:
            empty_directories.push(target)
            continue
```

`src/app/check/main.spl:293-299` consumes that second channel and seeds the
error count with it, so an unexpandable directory cannot exit 0:

```
    val (files, empty_directories) = expand_check_targets(raw_files)
    var checked = 0
    var errors = empty_directories.len()
    ...
        for directory in empty_directories:
            print "ERROR: {directory}: no Simple source files found"
```

`src/app/check/main.spl:104-111` additionally expands an existing path via
`find_spl_files` before target expansion. A live
`bin/simple check src/app/dashboard` was started and was still checking files
minutes later (i.e. demonstrably not a no-op), but did not finish inside this
lane's budget, so the closing evidence here is source content, not a quoted
verdict line.
