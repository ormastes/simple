# Cosmos PCIe/NVMe Pure-Policy Coverage

Run `sh scripts/check/check-cosmos-nvme-pcie-policy.shs` from the repository
root. The gate compares the pure-Simple owner against an independent frozen C
oracle over exhaustive bounded vectors, measures the narrow C pointer ABI
bridge with LLVM branch instrumentation, and requires both outcomes of every
named production predicate in the Simple policy manifest.

The receipt is deliberately scoped. It does not claim coverage of PCIe MMIO,
the complete Cosmos HAL, QEMU execution, or an unavailable physical board.
