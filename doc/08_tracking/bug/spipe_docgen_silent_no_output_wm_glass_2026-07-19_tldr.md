# SPipe Docgen Silent No-Output — TLDR

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

- Docgen exited 0 but created no mirrored WM glass manual.
- It printed unrelated compiler warnings and no focused result.
- Expected: artifact path/stub count or a nonzero focused diagnostic.
- The command was not retried; add a CLI output-existence postcondition.

```text
valid spec -> docgen exit 0 -> missing manual (BUG)
```

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro in the record, no status line existed); closed as stale per the "too old / not valid -> close" triage policy. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
