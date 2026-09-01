# Multi-architecture filesystem execution acceptance

Status: **SOURCE-CONTRACT — NOT LIVE-GUEST EVIDENCE**

This manual mirrors
`test/03_system/os/qemu/simpleos_multiarch_fs_acceptance_spec.spl`.

## Claim boundary

The executable specification creates in-memory candidate receipts to exercise
the pure-Simple acceptance validators. It proves neither a booted image nor a
filesystem mount. In particular, it does not turn an NVFS marker probe, a
FAT32-backed server entry, a Rust bootstrap binary, or a historical image into
current-source QEMU evidence.

## NVFS three-architecture campaign

`SimpleOsMultiarchNvfsCampaignV1` has a deliberately narrow contract:

1. The campaign contains exactly three candidates.
2. It contains x86_64, ARM64, and RV64 exactly once each.
3. Every candidate is a QEMU-system correctness row and says `filesystem=nvfs`.
4. Every candidate independently passes the existing ordered authenticated
   filesystem-launch lifecycle: mount, lookup, open-handle authentication,
   scheduler adoption, exit 37, one reap, address-space reclamation, and source
   handle close.

The validator rejects a missing/duplicate architecture, non-NVFS filesystem,
non-QEMU row, and any invalid lifecycle candidate. QEMU rows cannot include
native performance evidence.

## Current live boundary

Current x86_64, ARM64, and RV64 filesystem-server entries boot through FAT32
owners. Legacy `nvfs_probe` output is diagnostic only and is rejected as a
substitute for the NVFS receipt field. Thus every live NVFS row remains blocked
until a current admitted Pure-Simple compiler produces the three current-source
NVFS images and the canonical wrappers retain fresh target-bound receipts.

Do not run or admit this source-contract spec as a QEMU result. The future live
producer must use the current image, target, nonce, and cryptographically
admitted evidence path for each architecture.
