# Theme IPC K2 hard stop — TLDR

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

- K1 is landed; K2 remains open and fail-closed.
- Rejected K2 commits: `235ef0250b`, `41eedf1bf5`, `d9554f91af`.
- Three cycles are exhausted; no fourth repair is permitted.
- Final gaps: unregistered/unthreaded x86 compat IDs, direct-x86 interrupt
  stability bypass, incomplete old-layout audit, and RV32 `syscall6` ENOSYS.
- Resume from current `origin/main` with one real cross-architecture ABI table
  and audit all Simple/C/Rust/generated entry paths.
- No runtime syscall, SimpleOS, QEMU, event, pixel, timing, or RSS PASS exists.

```text
K1 owned bytes -> K2 registered ABI + real entry stability -> ThemeService
missing architecture/entry path -> fail closed
```

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro in the record, no status line existed); closed as stale per the "too old / not valid -> close" triage policy. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
