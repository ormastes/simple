# System test plan: SimpleOS on UP Squared Apollo Lake

REQ-001/002 and the offline portions of NFR-003/005 are covered by build/image
receipts and `--contract`. REQ-003 and NFR-001/002/004 are covered by the
separate media writer plus full readback receipt. REQ-004..007 and
NFR-005..008 require `--live` on the physical board.

`--ovmf` is the reproducible preflight for the exact admitted USB image. It
must prove the loader transition, ordered kernel markers, command-correlated
`ls /`, and VFS entries, but it never substitutes for physical `--live`.

Visible steps:

1. Identify UP Squared N4200 and console adapter.
2. Build/admit x86_64 UEFI USB image.
3. Select and verify removable USB target.
4. Write and read-back USB media.
5. Boot through board UEFI fallback `EFI/BOOT/BOOTX64.EFI`.
6. Observe ordered SimpleOS markers.
7. Run `ls /` on mounted root.
8. Retain and verify receipts.

Contract and self-test PASS are not physical evidence. Live absence is BLOCKED;
an observed entry followed by incomplete boot, or stale/non-VFS listing, is
FAIL.
