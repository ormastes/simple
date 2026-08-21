# SimpleOS 32-bit bootstrap live rows blocked

The shared source contract is implemented at `src/os/port/simpleos_32bit_bootstrap_contract.spl`, but this Linux worktree has no admitted source-matched compiler artifacts or fresh nonce-isolated QEMU receipts for x86_32, ARM32, or RV32. Source-contract success must not be promoted to live or target-native success.

Resume through Todo 834-836. Each row must retain compiler/phase/sysroot/linker/tool/image hashes and raw serial output, and must satisfy `simpleos-32bit-bootstrap-v2` without authored success markers.
