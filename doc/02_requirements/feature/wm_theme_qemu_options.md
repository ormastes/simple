# WM theme + QEMU requirement options

## F-1: Guest capture scope

### Option A — all supported desktop targets

Require x86_64, AArch64, and RISC-V source wiring plus live visual/input proof
when their target transport is available.

- Pros: matches the cross-architecture WM promise; prevents silent drift.
- Cons: completion depends on unavailable transport/host rows.
- Effort: L, 8–15 files/evidence artifacts.

### Option B — current-host AArch64 only

Require live proof only for macOS/HVF AArch64 and retain x86/RISC-V as planned
blocked rows.

- Pros: faster current-host milestone.
- Cons: weaker than the original all-SimpleOS objective.
- Effort: M, 5–9 files/evidence artifacts.

## F-2: Engine2D demo CSS behavior

### Option A — wire `/THEME.CSS` into every QEMU capture entry

Extend lightweight `gui_entry_engine2d.spl` capture/demo targets to mount and
apply the same override contract.

- Pros: any advertised QEMU visual capture can prove a custom Stitch theme.
- Cons: adds VFS/media dependency to lightweight demos.
- Effort: M, 3–6 files.

### Option B — keep demos baseline-only

Treat only `gui_entry_desktop.spl` as a custom CSS acceptance target.

- Pros: preserves small demo boot paths.
- Cons: capture scripts must never claim custom CSS coverage for demos.
- Effort: S, 2–4 docs/tests.

User selection is required before final requirements are written.
