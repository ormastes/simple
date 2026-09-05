# Theme IPC K2 hard stop — TLDR

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
