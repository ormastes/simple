# Cosmos NVMe PCIe Adapter Policy Migration Evidence — 2026-08-19

## Completed artifacts

- Pure-Simple scalar owner with a pinned 34-function production surface.
- Version-1 stable C ABI header with 39 total exported symbols.
- C adapter reduced to pointer/marshalling/callback/MMIO/DMA/barrier ownership;
  its scalar-policy closure is exactly 32 imports and its seven-function public
  ABI is unchanged.
- Independently named frozen C oracle and C-vs-Simple parity/coverage vectors.
- Host x86-64 and ARMv7 object/allocation/link gates with stub fallback disabled.
- Existing adapter contract routed through the admitted Simple-object gate.
- Canonical firmware/storage-link object wiring and source-receipt inventory.
- Exact 314-row parity inventory, compiler-emitted 46-location/92-outcome
  denominator with six helper exclusions, and an exact 98/98 LLVM C-bridge
  branch gate, all bound into the runtime receipt.

## Observed evidence

The original bounded gate reported:

```text
cosmos_nvme_pcie_adapter_static_abi_exports=39/39
cosmos_nvme_pcie_adapter_c_policy_imports=32/32
cosmos_nvme_pcie_adapter_c_public_abi=7/7
cosmos_nvme_pcie_adapter_frozen_oracle=independent
cosmos_nvme_pcie_adapter_branch_denominator=45 outcomes=90
STATIC_STATUS: PASS cosmos-nvme-pcie-adapter pure-policy migration
RUNTIME_EVIDENCE: NOT_RUN compiler=bin/simple mode=llvm-object targets=host,arm reason=compiler cannot be resolved through admitted provenance
STATUS: BLOCKED cosmos-nvme-pcie-adapter pure-policy runtime evidence
```

The only available `bin/simple` identifies itself as the Rust bootstrap seed and
has no admitted Stage 4 provenance. It was therefore not used to emit policy
objects or claim parity, coverage, contract, allocation, ARM, or link evidence.

A separate diagnostic-only Rust-seed check identified unparenthesized
multi-line boolean expressions in the partially started policy file. Those
expressions were corrected to the current Simple grammar. The diagnostic is not
acceptance evidence and was not retried after the bounded verification cap.

## Exact remaining evidence

The implementation now also closes the previously missing build/link and C
LLVM-coverage wiring. With an admitted Stage 4 executable and provenance
receipt, run
`scripts/check/check-cosmos-nvme-pcie-adapter-policy.shs` once. Remaining green
evidence is: host policy object and exact exports, no undefined/allocation
symbols, exactly 314 frozen-oracle parity rows, actual compiler-emitted 46/46
and 92/92 execution rows, adapter host contract against that object, 98/98 LLVM branch coverage for the C
bridge, ARM ELF32 object, and resolved ARM C-to-Simple relocatable link. The
receipt is intentionally absent until that admitted run passes.
