# Local research — Simple Container Improvement

**Date:** 2026-11-25
**Feature:** `simple_container_improvement`

The consolidated source audit lives in the architecture document
`doc/04_architecture/platform/container/simple_container_improvement.md` §3 ("What exists at the
verified main revision"), pinned to `main` @ `a214dc99348c`. It was produced by
direct inspection of the files listed in its §18.2 reference table and is the
authoritative local research for this feature. Key findings reused by increment 1:

- SCV object identity is `sha256_<hex>` (`src/lib/scv/store.spl`); preserved as
  the legacy alias format. New selectable-hash identities use the same
  `<algo>_<hex>` shape.
- Strongest existing publication discipline is compile-snapshot staged,
  read-back-verified, no-replace publication
  (`src/lib/scv/compile_snapshot.spl`, `file_publish_noreplace_raw`); reused as
  the store's publication pattern.
- SCV GC is dry-run-first and moves to quarantine, never unlinks
  (`src/lib/scv/gc.spl`, `maintenance.spl`); the store GC mirrors this.
- Pure-Simple XXH3 (`src/lib/common/hash/xxh3.spl`), BLAKE3
  (`src/lib/common/crypto/blake3.spl`), and a scalar GxHash 4.0.0 port
  (`src/lib/common/hash/gxhash.spl`, software AES sbox, no hardware AES
  requirement) already exist; no hash-provider/dispatch abstraction existed
  before this feature.
- Container contracts are value-only structs with fail-closed admission-reason
  functions (`src/lib/common/contracts/container/host_capability_v1.spl`,
  `runtime_v1.spl`); Simple has no trait syntax for mutable provider ports.
- `container_storage.spl` is explicitly a pure model (no I/O); the runtime
  provider reports no durable recovery — both recorded as later-phase work.

# Domain research

External primary sources (Linux cgroup v2, OverlayFS, Windows HCS/job objects,
FreeBSD jails/rctl, Apple App Sandbox/Mach-O, GxHash/xxHash/BLAKE3 upstream,
RISC-V scalar crypto, Google Agent Substrate on GKE) are collected and cited in
`doc/04_architecture/platform/container/simple_container_improvement.md` §18.3 (W01–W18), checked
2026-11-25. Increment 1 (hash policy + immutable store + contracts) relies only
on the hash-algorithm sources (W10–W12, W18); platform sources gate later
phases.
