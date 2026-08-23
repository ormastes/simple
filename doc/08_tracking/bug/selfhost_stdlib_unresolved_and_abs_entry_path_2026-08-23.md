# Self-hosted stage2: stdlib does not resolve for a real spec; absolute entry path collects zero sources (D4)

- Date: 2026-08-23
- Severity: HIGH (blocks compiling any real spec with the self-hosted binary)
- Status: OPEN (filed, not fixed)
- Area: entry/source resolution + stdlib module resolution in the bootstrap CLI

## Symptom A -- stdlib does not resolve

Compiling a real spec with stage2 reports unresolved stdlib names:

```
unresolved name: file_read_result
unresolved name: read_file_text_result
unresolved name: runtime_file_rename
   at src/std/nogc_sync_mut/io/file_ops.spl:7:8
```

These are stdlib symbols in a stdlib file, so this is a resolution failure inside
`src/std`, not user-code error. Per `.claude/rules/commands.md` the stdlib is read
as SOURCE on every run (82 `.spl` opens, zero `.smf`), so no build step should be
required for these to resolve.

## Symptom B -- absolute entry path collects zero sources

Passing an ABSOLUTE path as the entry yields `collected zero source files`, while
a repo-root-relative path is collected. The entry resolver appears to require a
repo-root-relative path.

This is a fail-open shape worth calling out on its own: "collected zero source
files" is reported where an unusable entry path should be a hard error naming the
path it could not resolve. A build that compiles nothing must not look like a
build that succeeded.

## Status of verification (honest)

Symptom A and B are recorded as REPORTED from the initiating investigation and
are NOT independently re-derived in this record. The stage2 binary they were
observed on is
`/mnt/data/bootstrap-run28/stage2/x86_64-unknown-linux-gnu/simple`
(132,930,184 bytes, commit `9c5e2dad378`).

Next step for whoever picks this up: confirm both against that binary with exit
statuses read directly into a variable, then determine whether Symptom A is a
consequence of Symptom B (a truncated source set would leave stdlib imports
dangling) -- the two may well be one defect, and that should be established
before either is fixed.
