# Cosmos NVMe PCIe Adapter Policy Boundary

## Status

The adapter's allocation-free scalar decisions are owned by
`cosmos_nvme_pcie_adapter_policy.spl`. The stable C ABI is version 1 and is
declared by `cosmos_nvme_pcie_adapter_policy.h`.

## Ownership boundary

Pure Simple owns command identity extraction, opcode classification, common and
opcode-specific field validation, transfer-size overflow checks, PRP span
validation, admin payload sizing, completion-result mapping, and scalar service
initialization admission.

The exact Simple-owned production denominator is 34 functions. The admitted
coverage denominator comes from compiler-emitted rows for 46 exact tagged
source locations and 92 outcomes. This includes both locations of the repeated
PRP-second-alignment predicate. Six branches in legacy coverage-audit helpers
are tagged and excluded explicitly. The older 45-name/90-bit owner mask remains
ABI-compatible diagnostic data and is not acceptance evidence.

C owns pointer/null admission, descriptor and service-structure marshalling,
callback invocation, volatile staging-buffer writes, MMIO, DMA submission and
polling, data barriers, and queue/completion publication. The C owner imports
the 32 policy functions needed by those mechanisms; it does not retain a second
copy of scalar policy.

`cosmos_nvme_pcie_policy.spl` remains the owner of PCIe queue/status-word
policy, and `cosmos_pcie_residual_policy.spl` remains the owner of residual
transport policy. Neither surface is part of this adapter migration.

## Stable ABI and object contract

- ABI version: `1`
- Public policy exports: `39` (`34` production scalar functions plus `5`
  closed coverage-audit functions)
- C adapter policy imports: `32`
- C adapter public ABI: unchanged at `7` functions
- Runtime/allocation dependencies permitted in a policy object: none
- Required targets: ELF64 x86-64 host and ELF32 ARM

The ARM relocatable link must resolve every
`cosmos_nvme_pcie_adapter_policy_*` import from the C owner. Other hardware
imports remain intentionally owned by the firmware link.

The production Cosmos build, storage-link contract, and immutable source
inventory each include the adapter policy source/object. Every emission uses a
private cache and re-verifies the admitted Stage-4 compiler and provenance.

## Evidence policy

The independent oracle uses only
`cosmos_nvme_pcie_adapter_oracle_*` names and is compiled separately. Its object
must neither define nor import a production policy symbol. Parity vectors link
that oracle with the emitted pure-Simple host object.

The scoped denominator is pinned to 46 compiler-emitted production decisions,
92 outcomes, six helper exclusions, and exactly 314 independent-oracle parity
rows. Every tagged production location must emit exactly one runtime row with
both outcomes. Host parity/coverage and both Simple object gates run
only with admitted Stage 4 provenance and `SIMPLE_NO_STUB_FALLBACK=1`. If that
compiler is absent, the gate exits nonzero and reports `RUNTIME_EVIDENCE:
NOT_RUN`; Rust-seed output is diagnostic only.

The same admitted run instruments only `cosmos_nvme_pcie_adapter.c` with LLVM
source coverage and requires the exact 98-branch denominator with every branch
covered. The adapter-only harness supplies service initialization locally, so
it neither aliases nor links the separately owned media policy/oracle ABI.
The receipt binds the exact named-decision manifest, LLVM report, compiler,
provenance, sources, oracle, vectors, host/ARM objects, and resolved ARM link.
