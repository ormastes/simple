# Freestanding Entry Constants Become Zero Stubs

Status: OPEN (P1) — **kept open deliberately; NOT verified either way.** The row
has no reproduction recipe and its named artifact no longer exists in the tree.
See "Re-triage 2026-08-17".
Status re-verified 2026-08-17 by source inspection (triage shard 01).
  (Do not trust that stamp; it is not backed by anything reproducible.)

## Re-triage 2026-08-17 — unreproducible on this host, left OPEN

Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
the stale Rust seed. No freestanding native build was run (~15 lanes share this
checkout; rebuilding/redeploying is prohibited).

Findings:

1. **The named subject file is gone.** `gui_entry_desktop.spl` does not exist
   anywhere under `src/` or `scripts/` (`find` + `grep -rl`, both empty), and
   `git ls-files 'src/os/**' | grep entry` lists no replacement carrying `FB_W`,
   `FB_H`, or `DIRECT_QEMU_TOTAL_MEMORY`. The only surviving near-match name is
   `src/os/kernel/arch/arm64/ramfb.spl:17` (`val ARM64_RAMFB_WIDTH: u32 = 1024`),
   an unrelated module-level `val`. Its last deletion appears in
   `6f86ff32a7db`, which CLAUDE.md records as the fourth tree-wipe commit, so
   the deletion may itself be wipe damage rather than an intentional removal —
   that is not resolved here.
2. **Half of the "Required Fix" is present.** `global_init_values` IS preserved
   through per-module mangling:
   `src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs:263-292`
   ("Phase 2: Rename globals in mir.globals, global_init_values,
   local_globals") re-keys every `global_init_values` entry to the mangled name,
   with the parallel `global_init_strings` map handled the same way.
   `mir.local_globals` is likewise re-keyed (lines 336-341).
3. **The other half — entry-module `Node::Let` classified as data — is NOT
   confirmed.** `grep 'Node::Let'` over `native_project/mod.rs` returns nothing;
   the only `is_entry` uses there (lines 959-968, 1340, 1374-1379, 1517-1526)
   concern `main`->`spl_main` renaming and object-cache eligibility, not global
   classification. So there is no positive evidence that an entry-file
   module-level scalar `val` is emitted as initialised data rather than left
   undefined and then fabricated as a weak zero-returning body by
   `native_project/stubs.rs`.

**Why this stays OPEN rather than being retired:** the mechanism in item 3 is
unverified, and a wrong close loses a real, silent, wrong-answer defect in
kernel hardware bring-up. Retiring on "the file that showed the symptom was
deleted" would be classification by absence, not by content.

**What the next lane needs (this row currently has none):** an actual
reproduction — a two-file freestanding tree, entry file declaring
`val PROBE_W: u32 = 1024` read by an imported function, built with
`native-build --target x86_64-unknown-none --emit-archive`, then
`nm`/`readelf -sW` asserting `…__PROBE_W` is an `OBJECT` in a data section and
**not** an 8-byte `WEAK FUNC`. That is the missing control; without it neither a
fix nor a retirement can be proven.

Stage3 Cranelift freestanding builds emit module-level scalar `val`s declared
in the entry file as weak functions returning zero instead of initialized data.
Imported module constants are emitted as initialized data.

## Evidence

`gui_entry_desktop.spl` symbols such as `FB_W`, `FB_H`, and
`DIRECT_QEMU_TOTAL_MEMORY` appeared as weak text symbols whose bodies were
`xor eax,eax; ret`. Consequently PMM received zero bounds and BGA received a
zero requested mode, while PCI discovery itself remained valid.

## Required Fix

The native-project data-export/mangling pass must classify entry-module
`Node::Let` immutable globals as data and preserve `global_init_values` through
per-module compilation. Until fixed, early freestanding entry hardware values
are local immediates at their owning operations. They must not be replaced by
fake device readback or fixed evidence metadata.
