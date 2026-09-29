# VFS Contract V1 detail design

**Status:** source-landed contract; runtime qualification remains separate.

`VfsContractV1` is a provider-neutral, pointer-free value seam:

```text
platform consumer -> VfsRequestV1 -> SOSIX validation/copy -> provider
                                              <- validated owned result <-
```

It owns portable absolute-path normalization, open-flag/rights admission,
generation-bearing file identity, stat/directory/watch shapes, correlation,
and fixed cardinality/byte bounds. Invalid requests never invoke a provider.
Rejected, oversized, malformed, or uncorrelated provider responses are
replaced by empty suppression results. Accepted nested arrays are copied.

The SimpleOS adapter reuses `fs_driver.types.Path` and `OpenFlags` only at the
platform boundary. It does not call the kernel ABI, mount storage, implement
NVFS, or claim persistence/durability. Those mechanisms remain behind the
existing SimpleOS VFS/provider and NVFS service layers.

Focused executable behavior is in
`test/01_unit/os/sosix/vfs_contract_adapter_v1_spec.spl`.
