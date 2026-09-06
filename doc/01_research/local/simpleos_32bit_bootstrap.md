# SimpleOS 32-bit bootstrap — local research

The repository has separate x86_32, ARM32, and RV32 target knowledge, but live
bootstrap evidence needs one shared admission boundary. The canonical owner is
`src/os/port/simpleos_32bit_bootstrap_contract.spl`; its profiles bind each
architecture to a target triple, ABI, linker emulation, sysroot/tool manifests,
and QEMU executable. The focused unit spec exercises complete and malformed
receipts without claiming that QEMU ran.

A trustworthy v2 receipt needs distinct Phase 1 and Phase 2 hashes, Phase 2
parent lineage, no-stub mode, nonzero manifest/linker hashes, exit status 37,
and one fresh 16+ character nonce across guest entry, filesystem execution,
reap, and final-pass markers. Todo 834-836 remain the live x86_32, ARM32, and
RV32 operator gates. Their retained artifacts belong below
`build/test-artifacts/simpleos_32bit_bootstrap/<arch>/`.

