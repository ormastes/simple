# ARM64 PCI upstream interface audit

Read-only source trace at `a41511004a0`; no build or native claim. Sent to SimpleOS repair owner.

## Existing descriptor contract

`src/os/drivers/pci/pci_provider.spl:19` defines `PciHostDescriptor`: provider, domain, bus_start/end, ecam_base/size, windows, dma_base/size, coherent. `PciAddressWindow` retains distinct PCI and CPU bases. `pci_host_descriptor_reason:32` validates presence, ECAM extent, bus capacity and windows. `pci_host_config_addr:51` returns `Result<u64,text>` and accounts for bus_start. The caller must additionally enforce hardware-specific target alignment/device/function limits and address overflow where required.

Only existing production constructor found: `src/os/kernel/arch/riscv64/starfive/pcie_host.spl:13`, `starfive_jh7110_pcie1_host_from_validated_dtb`. This accepts already validated numeric resources; it is not a generic DTB parser. Its firmware-default helper explicitly limits itself to contract tests until compared against preserved DTB. `starfive/nvme_probe.spl:41,47` demonstrates checked config read/write using `pci_host_config_addr` then MMIO.

No ARM64 constructor or PCI DTB decoder exists in the inspected owner trees.

## Firmware handoff gap

Active examples ARM64 `boot/crt0.S` explicitly ignores firmware x0. Early banners/EL setup overwrite x0 before `_c_start` at line 211; C `_c_start(void)` at `baremetal_stubs.c:1508` calls zero-argument `spl_start`. DTB therefore must be preserved before early calls and relocation, published after BSS initialization, and handed to a boot-owned parser before PCI access. A guessed address cannot recover it.

The separate `src/os/kernel/arch/arm64/boot.spl:204` accepts dtb_addr but does not consume it. It is not the examples boot path. Limine boot retains RSDP in BootOutputPort; no PCI descriptor producer was found there. Legacy C `baremetal_stubs.c:1191` hardcodes ECAM_BASE; that is not a validated descriptor source.

## Reusable FDT boundary

`src/os/kernel/boot/fdt_blob.spl`: `FdtBlob.at_address:40`, `from_bytes:54`, `valid:68`, `fdt_find_compatible:340`, `fdt_node_prop:183`, `fdt_node_u32:210`, `fdt_node_reg:239`. Physical mode is explicitly MMU-off/identity; byte fixtures use the same reader. Compatible search filters enabled nodes.

FdtNode addr_cells/size_cells describe its parent. `fdt_node_reg` decodes only one/two-cell addresses; it cannot decode PCI ranges. A dedicated PCI parser must consume node-owned cell sizes, child PCI flags/address, parent CPU address and size, retaining translation in PciAddressWindow. Read bus-range and ECAM reg with exact shape checks; reject unsupported topology/missing ranges instead of selecting defaults. The generic reader does not apply ancestor ranges translation. Restrict the accepted topology or validate ancestors rather than assuming identity.

Property accessor returns off/len without validating the full extent, and byte() returns zero beyond blob size. The PCI parser must reject truncated properties explicitly before using values. Bound compatible-host count and property/range count, fail closed for malformed/ambiguous hosts, and expose the absence to callers before any MMIO write.
