# Merge e274cd33719 clobbered x86_64 SimpleOS boot-lane sources (2026-08-31)

**Class:** stale-snapshot clobber (same family as the sync-clobber incidents in
`.claude/rules/vcs.md`). Commit `e274cd33719` "chore: merge all share-history
worktree branches into main" (992 files, +64,136/-46,226) replaced several
SimpleOS boot-lane sources with OLDER generations, turning
`check-simpleos-x86-64-wm-qemu-preflight.shs` and
`check-simpleos-x86_64-crt0-args.shs` RED while every push guard stayed green
(they check tree structure, not lane semantics).

## What was lost (verified two-way, pre-merge blob vs post-merge blob)

| File | Damage | Restored from |
|---|---|---|
| `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl` | 660→347 lines; lost `install_generated_simpleos_wm_theme()` call + theme evidence, `simpleos_hda_start()` wiring, VRAM probe, taskbar-clock pin, HDA calibration. Only post-merge additions were comment noise. | `e274cd33719~1` (strict functional superset) |
| `src/os/compositor/engine2d_baremetal_core.spl` | 389→166 lines; lost the entire SIMD dispatch surface (`rt_gui_simd_fill_enabled/hits/chunks/tail_pixels` externs + `baremetal_simd_fill_*` accessors) that BOTH desktop entries import — tree did not even resolve. | `e274cd33719~1` (superset; no current-only functions) |
| `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c` | 20,197→17,973 lines; 27 `rt_*` providers dropped incl. `rt_pci_enable_memory_bus_master`. The 3 apparent post-merge-only ed25519 symbols exist pre-merge too (formatting differences). | `e274cd33719~1` |
| `src/os/libc/simpleos_crt0.S` | Bounded CRT launch-args contract from `8b7965c37a9` ("fix(simpleos): deliver bounded CRT launch arguments") reverted to the argc=0/NULL stub by `4edef8fab8e` "snapshot current development state" (then carried by the merge). | `8b7965c37a9` |

## Verification after restoration (this host, 2026-08-31)

- `check-simpleos-x86-64-wm-qemu-preflight.shs` →
  `simpleos_x86_64_wm_qemu_preflight_status=pass` (was
  `fail/generated-theme-snapshot-not-installed`, then three further reasons as
  each layer was peeled).
- `check-simpleos-x86_64-crt0-args.shs` →
  `PASS: x86_64 SimpleOS CRT argument and startup-order contract`
  (was exit 1, `cmp r12, 64` bounded-argv path absent; the gate assembles and
  links the CRT, so this is a functional check, not a text one).

## Not audited here

The merge touched 992 files; only the x86_64 boot-lane surfaces gated by the
scripts above were audited and repaired. Other subtrees (e.g. `src/os/userlib`)
may carry the same mixed forward/backward damage and deserve the same two-way
(pre-merge vs post-merge) symbol-set diff before trusting either side.
