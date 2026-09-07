# `main`'s `.spipe/spipe` gitlink points at a commit that exists on no SPipe remote

Date: 2026-09-06. Found while re-landing PR #371 after PR #375 ("session-cleanup") merged.

## Symptom

`git ls-tree origin/main .spipe/spipe` → `3db4e4e`. That commit was made on 2026-09-05 in a
LOCAL `.spipe/spipe` checkout (the ≥90 sspec checklist edit) and was never pushed as-is: it
reached `ormastes/Spipe` only after being rebased onto SPipe `origin/main`, where it became
`06d7d34`. `git -C .spipe/spipe branch -r --contains 3db4e4e` is empty.

Consequence: on a fresh clone of `main`, `git submodule update --init .spipe/spipe` fails to
fetch `3db4e4e`; the checklist file every sspec worker is told to read does not materialise, and
`sspec-train.shs --split private_test` ERRORs fail-closed (`checklist file not found`).

## How it got there

PR #375 committed the shared checkout's working copy wholesale
(`e2f78c42716 chore(session): commit the in-flight web-renderer/spipe work`), which captured the
submodule's then-detached local HEAD as the gitlink. This is the "sync must never clobber"
class in `.claude/rules/vcs.md` applied to a gitlink: a whole-WC commit snapshotted a pointer
that only meant something on one machine.

## Fix

PR #371 (`work/debug-perf-dump-skills-2026-09-05`) pins the gitlink to `06d7d34`, which is on
SPipe `origin/main`; `.spipe/training/splits.sdn` freezes the checklist digest against that
same content (`sha256:dd830096…`). Verified fresh-clone form: `git submodule update --init`
→ `06d7d34` → `PASS — 14 checked, split=private_test, target=90`.

## Prevention (not done — proposal)

A push-tier guard row that, for every gitlink in the outgoing range, runs
`git -C <submodule> branch -r --contains <sha>` and FAILs when empty. Same fail-closed shape as
the other guards; a range with zero gitlink changes is `PASS — 0 gitlink(s) changed`, not ERROR,
since absence of a gitlink change is a positive fact here.
