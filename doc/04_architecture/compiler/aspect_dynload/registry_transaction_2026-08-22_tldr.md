<!-- codex-architecture -->
# Aspect Registry Transaction — TLDR

- `AspectRuntimeRegistry` is the sole mutable loader authority.
- One mutex protects slots, packs, facets, pools, counters, generations, pins,
  retirement and snapshot publication; no I/O, mapping, callbacks,
  destruction, or waiting occurs while held.
- Activation stages off-registry. `Active` is final record initialization;
  immutable snapshot installation is the later visibility mutation.
- Single-flight results are stable per attempt; retry is explicit.
- Readers acquire/release registry-counted immutable snapshot leases and use
  nonce-bearing live generation pin tokens; no lock-free pointer is assumed.
- Quiesce blocks new pins; final pin release retires Code/Data/RoData/BSS as
  one ownership batch, with partial failure retained and poisoned.
- One descriptor is used to copy and digest an immutable owned extent; all lazy
  reads/maps use those bytes. Path reopen and mutable file-backed pages are banned.
- Dependency cycles are detected by a task-local execution-context stack.

Next: `doc/05_design/compiler/aspect_dynload/registry_transaction_2026-08-22.md`.
