# ARM filesystem-exec root routing contract

This unit contract protects the ARM64 FAT32 root-file route used by the QEMU
filesystem-execution acceptance lane.

It proves statically that:

- `/FSEXEC.ELF`, `/SIMPLE.ELF`, and `/HELLO.SPL` are handled before generic
  `/SYS/APPS/` prefix dispatch;
- root directory scans use the BPB-derived root cluster rather than assuming
  cluster 2; and
- the alias and FAT 8.3 directory-entry contracts retain `FSEXEC  ELF`.
- the two fabricated definitions that survived in the retained ELF,
  `rt_array_copy` and `rt_enum_id`, have real ARM64 runtime bodies.

The test is intentionally static because the originating ARM64 lane exhausted
its three permitted build/boot cycles. A later clean session must still rebuild
and boot the guest to prove the runtime repair.
