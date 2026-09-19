# SCV freeze refused: symlinked .spl sources cannot pass the no-follow admission reader

Date: 2026-09-18
Lane: release v1.0.0-beta line (kimi-20260915-beta2)
Severity: release-blocking (windows-x86_64 leg, 83 minutes into the compile)
Status: fixed in v1.0.0-beta.13

## Symptom

v1.0.0-beta.12's windows-x86_64 worker compiled for 83 minutes, then:

```
SCV-E-SNAPSHOT: snapshot-read-failed:src/app/debug/coordinator.spl
SCV freeze has no admitted source inventory to freeze the entry closure against.
Refusing to compute an entry closure under the default fail-closed policy.
```

## Cause

`src/app/debug/coordinator.spl` (and 10 more files under `src/`) are git
SYMLINKS, e.g. `src/app/debug/coordinator.spl ->
../../lib/nogc_sync_mut/debug/coordinator.spl` (dedup of identical tool
sources). The SCV compile-snapshot admission reader is deliberately
no-follow (`scv_compile_snapshot_read_source_v1` ->
`file_read_regular_no_follow_bounded`, src/lib/scv/compile_snapshot.spl:109):
on unix `O_NOFOLLOW` makes open() fail on a link, and on Windows the reader
rejects `FILE_ATTRIBUTE_REPARSE_POINT`. Either way one unreadable file
invalidates the whole snapshot inventory, and the entry-closure freeze then
has nothing to freeze against. Fail-closed by design — a symlink could
smuggle out-of-tree content past admission.

The tree has carried 66 symlinks (11 under `src/`); repo history shows
repeated squash damage and repair ("restore N symlinks ... with
content-as-target"), i.e. the plain-file state is one the tree has lived in
before. Earlier betas never reached the freeze phase, so this never fired.

## Fix

Replaced the 11 `src/` symlinks with copies of their target content
(src/app/debug/*, src/app/leak_finder/*, src/app/lint/main.spl). No symlink
remains under the admitted source roots, so the no-follow reader admits every
file. Trade-off: the 11 files are now duplicates of their
src/compiler/90.tools + src/lib/nogc_sync_mut counterparts and can diverge
under future edits — the pre-squash history accepted the same trade-off
(content-as-target states passed CI).

The remaining 55 symlinks (.claude/commands, docs tooling) are outside the
SCV source roots and were left alone.

## Note

`SIMPLE_SCV_FREEZE_FALLBACK=1` (the in-message remedy) was NOT used: it opts
into an unfrozen filesystem scan and would weaken the release-integrity gate
this repository mandates.
