# SimpleOS 32-bit bootstrap agent plan

| Lane | Owner | State |
|---|---|---|
| Shared contract/spec/manual | this lane | implemented |
| x86_32 QEMU receipt | prepared QEMU operator | blocked: TODO 834 |
| ARM32 QEMU receipt | prepared QEMU operator | blocked: TODO 835 |
| RV32 QEMU receipt | prepared QEMU operator | blocked: TODO 836 |
| Sidecars | N/A | bounded single-owner contract |

Merge owner and final normal/highest-capability reviewer: parent/root agent. Retain receipts beneath `build/test-artifacts/simpleos_32bit_bootstrap/<arch>/`.
