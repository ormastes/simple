# NVMe FW RV64 direct build terminates before ELF output

Status: OPEN
Date: 2026-07-07

## Repro

```bash
NVME_RV64_BUILD_TIMEOUT_SECS=120 sh examples/09_embedded/simpleos_nvme_fw/fw_rv64/build.shs
```

## Observed

The script creates a tiny generated entry and invokes:

```bash
bin/simple native-build --backend llvm \
  --source build/os/generated \
  --source examples/09_embedded/simpleos_nvme_fw/fw_rv32 \
  --entry build/os/generated/nvme_fw_rv64_direct_entry.spl \
  --entry-closure \
  --target riscv64-unknown-none \
  --emit-object -o build/test-artifacts/nvme_fw_rv64.o
```

The compiler is terminated before `build/nvme_fw_rv64.elf` is produced. Last
observed phase:

```text
phase2:parse:file:start examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_ecc.spl
Terminated
```

## Expected

The build completes and produces `build/nvme_fw_rv64.elf`, allowing
`examples/09_embedded/simpleos_nvme_fw/fw_rv64/boot.shs` to satisfy the RV64
real-boot SSpec.

## Notes

The first implementation generated one large concatenated source file; that was
fixed by importing the existing split `fw_rv32` logic modules directly. The
remaining failure is native-build throughput or external termination, not a fake
boot pass.
