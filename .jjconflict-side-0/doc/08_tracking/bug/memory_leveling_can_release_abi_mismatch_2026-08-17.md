# MemoryLevelingManager missing `can_release` — kernel-build ABI mismatch (RESOLVED 2026-08-17)

Lane W16-A. Unblocks `scripts/check/check-enterprise-store-in-guest-ovmf.shs`
(enterprise-store in-guest board-runnable gate).

## Reproduced diagnostic (before fix)

Kernel build (Rust seed, `native-build --target x86_64-unknown-none`, the exact
command the OVMF gate runs) failed at codegen:

```
[CODEGEN BODY] Function 'MemorySwapCoordinator.can_release_swapped' body compilation failed:
callable ABI mismatch for 'src__lib__nogc_sync_mut__io__dma__SharedDmaMapping_dot_can_release':
Instance target declares 1 parameter(s), call supplies 2 explicit argument(s) and 1 receiver slot(s)
[CODEGEN BODY] Function 'memory_swap_runtime_can_release_range_in' body compilation failed: <same>
... 1 function body/bodies failed to compile: [MemorySwapCoordinator.can_release_swapped]
EXIT=1
```

Call sites (both pass 2 explicit args):
- `src/os/kernel/memory/memory_swap_coordinator.spl:234` — `me.manager.can_release(allocation_id, owner_id)`
- `src/os/kernel/memory/memory_swap_runtime.spl:131` — `manager.can_release(mapping.allocation_id, owner_id)`

## Root cause

`MemoryLevelingManager` (`src/os/kernel/memory/memory_leveling_manager.spl`) had
**no `can_release` method**. The name resolved to the only visible
`can_release` in scope — `SharedDmaMapping.can_release()` in
`src/lib/nogc_sync_mut/io/dma.spl:193`, which takes only `self` (1 param). The
two call sites pass `(allocation_id, owner_id)`, so the compiler reported "1
declared, 2 supplied". The call sites are CORRECT (they want a read-only
release-eligibility predicate on the manager); the manager declaration was the
missing half.

## Fix (declaration side)

Added the missing read-only predicate `can_release(allocation_id, owner_id) ->
MemoryLevelingOperation` to `MemoryLevelingManager`, mirroring `release`'s
pre-mutation gating (not-found / not-owner / protected / released) but WITHOUT
mutating state or stats. Behavior preserved: `can_release_swapped` and
`release_swapped` already expected exactly this contract (gate first, then
`release`), and `release` re-checks the same conditions before mutating, so the
predicate is a faithful non-mutating mirror. No call site or param was deleted.

## Verification

- Clean-cache rebuild WITH fix: `EXIT=0`, no ABI errors, kernel elf produced
  (`build/os/simpleos_entstore_uefi128.elf`, 2703896 bytes).
- Toggle proof: reverting the file reproduces `EXIT=1` with the exact diagnostic
  above; restoring gives `EXIT=0`.
- `scripts/check/check-enterprise-store-in-guest-ovmf.shs` (real OVMF pflash ->
  GRUB-EFI multiboot boot; NOT `-kernel`, NOT isa-debug-exit) now:
  `PASS — 6 rung(s) checked` — L1 grub-uefi multiboot, L2 SSH+ring-3, L3 probe
  begin, L3.5a direct write rc=0, L3.5b facade write+read-back=OK, L4 enterprise
  store open=true verify=[]. Transcript:
  `build/os/entstore/ent_store_in_guest_ovmf.serial.log`.

Runner: Rust seed at
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`
(59536728 bytes, mtime 2026-08-16 22:59:37). `bin/release` not overwritten.

## Files changed

- `src/os/kernel/memory/memory_leveling_manager.spl` — added `can_release`.
