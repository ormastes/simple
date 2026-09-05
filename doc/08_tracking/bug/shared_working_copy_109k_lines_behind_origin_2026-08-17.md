# Shared working copy is ~109,000 lines behind origin — any whole-WC commit reverts landed work

- Date: 2026-08-17
- Area: infra / VCS / multi-session hygiene
- Severity: high (a single `jj commit -a` / `git add -A` from any session
  reverts up to ~109k lines of landed work across 1,243 files)
- Found by: `.spipe/simple_enterprise_suite` sync pass

## Symptom

Measured on the shared checkout at `/Users/ormastes/simple` with
`main@origin = 0b88b24533f1`:

```
git diff --stat 0b88b24533f1
  1243 files changed, 21520 insertions(+), 109001 deletions(-)
```

The 109,001 "deletions" are landed upstream content ABSENT from the working
copy; the 21,520 "insertions" are, in every case sampled, OLDER pre-hardening
content that upstream has already superseded.

Concrete instances found while repairing one lane's paths:

| Path | WC state vs origin |
|------|--------------------|
| `.spipe/simple_enterprise_suite/state.md` | 756 lines behind |
| `doc/07_guide/lib/database/enterprise_store.md` | 457 lines behind |
| `src/lib/nogc_sync_mut/enterprise_store/store.spl` | 260 lines behind |
| `src/lib/common/net/http_core.spl` | 159 lines behind |
| `src/lib/nogc_sync_mut/enterprise_store/audit_hash.spl` | ABSENT |
| `src/lib/nogc_sync_mut/enterprise_store/file_backend.spl` | ABSENT |
| 18 of 28 enterprise spec files | ABSENT |
| `examples/12_business/simple_erp/ubs_test/*` | pre-AC-14 in-memory form |

## Why it matters

This is the precondition for the exact accident `.claude/rules/vcs.md`
§"Sync must never clobber" describes, and which this repo has already suffered
(`118c636ead8`: 109,375 files → 4). The lane's own state file records a near
miss on 2026-08-16: *"a concurrent session staged deletion of the entire
enterprise stdlib + simple_erp example in the shared WC; restored from HEAD per
anti-revert protocol."*

The pre-push tree-size guard (`check-tree-size-push.shs`) catches a wiped TREE,
but a whole-WC commit built from a stale-but-populated checkout can land inside
the ±0.15% band while still reverting thousands of lines in individual files —
the guard counts files, not content freshness.

## Root cause

The working-copy commit `@` is a long-lived conflict commit whose base predates
155 upstream commits. Sessions keep editing files in it without ever bringing
the checkout forward, so the WC accumulates stale copies of paths that other
sessions have since landed.

## What was done

Only one lane's surface was repaired (forward-only, both directions diffed per
vcs.md before each restore): the `enterprise_*` lib modules, `src/app/
enterprise{,_store_app}`, both `http_server` trees, `common/net`, that lane's
spec directories, `examples/12_business/simple_erp`, and its guides/wiki/state.
The 52 files conflicted from other lanes' uncommitted work were deliberately
left untouched — resolving another session's in-flight edits is itself a
clobber risk.

**The remaining ~1,200 files are still stale.** They are not safe for any
session to whole-WC-commit.

## Suggested fix

1. Each active session brings ITS OWN paths forward from `main@origin`
   (`jj restore --from main@origin <paths>`) after diffing both directions,
   rather than one session sweeping the whole tree.
2. Add a pre-push content-freshness check to complement the tree-size guard:
   for every path in the outgoing range, fail when the commit reverts a file
   to an older version of content already on `main@origin` and the committer
   did not author the change (the "revert guard" vcs.md already describes as
   manual — this is the case for automating it).
3. Longer term: stop using one shared working copy for many parallel sessions;
   per-session worktrees make staleness impossible to accumulate silently.
