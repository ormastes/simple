# Cosmos NVMe PCIe Adapter Pure-Policy Evidence

Run:

```text
scripts/check/check-cosmos-nvme-pcie-adapter-policy.shs
```

The gate checks the exact 39-symbol version-1 ABI, the exact 32-symbol C import
closure, the unchanged seven-function adapter ABI, independent frozen-C-oracle
symbols, strict C compilation for host and ARM, no policy stubs, and the pinned
45-decision/90-outcome denominator.

With an admitted pure-Simple Stage 4 compiler, it additionally emits
allocation-free host and ARM policy objects, runs C-vs-Simple parity vectors,
executes the adapter contract against the Simple object, proves 45/45 decisions
and 90/90 outcomes from actual calls, and performs the ARM relocatable link.

Without admitted Stage 4 provenance the runtime section fails closed with exit
status 2 and `RUNTIME_EVIDENCE: NOT_RUN`. Static evidence remains explicitly
separate and must not be reported as runtime or target-object proof.
