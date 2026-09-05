<!-- codex-research -->
# Domain Research: CXL-Friendly Device Processes

Date: 2026-08-02  
Status: research complete; requirements selection pending

## Conclusions

The external evidence supports a hybrid microkernel/exokernel model: keep
protection and revocation in the kernel, place device policy and protocols in
user components, and use typed control IPC plus shared asynchronous data paths.
It does not support treating CXL as an execution engine.

## Primary-source findings

### CXL revision and scope

The CXL Consortium identifies CXL 4.0 as the current specification. Its
November 18, 2025 release describes 128 GT/s operation, bundled ports, and
enhanced memory RAS. SimpleOS may design a revisioned capability vector that can
represent these features, while beginning with the CXL 2.0-era Type 3 behavior
that QEMU can exercise.

Sources:

- [CXL Consortium overview](https://computeexpresslink.org/about-cxl/)
- [CXL 4.0 specification release announcement](https://computeexpresslink.org/wp-content/uploads/2025/11/CXL_4.0-Specification-Release_FINAL_Website-Copy.pdf)

Type 1 is a cache-capable accelerator, Type 2 is an accelerator with
host-managed device memory, and Type 3 is a memory device. None of those type
labels guarantees that SimpleOS can load and isolate an arbitrary driver on the
endpoint. A programmable execution environment, secure loader, interrupt/DMA
access, host transport, watchdog/reset, update policy, and attestation remain
separate prerequisites. This is an architectural inference from the device
roles, not a CXL conformance guarantee.

Sources:

- [QEMU CXL device model and device types](https://www.qemu.org/docs/master/system/devices/cxl.html)
- [CXL Consortium memory form-factor discussion](https://computeexpresslink.org/blog/cxl-memory-form-factor-comparison-examination-of-form-factors-for-this-growing-standard-1027/)

### QEMU evidence boundary

QEMU documents a static, single-host CXL model that ignores fabric management
and does not emulate the coherency protocol. It can functionally model PCI
configuration, BARs, MSI-X, AER, DOE, memory, host bridges, root ports,
switches, Type 3 devices, interleave, volatile/persistent capacity, and Arm
`virt,cxl=on` topologies. This is appropriate for CXL discovery through RAS and
hot-remove behavior, but not for coherence latency, multi-host ownership, or
fabric completeness.

QMP exposes CXL poison, general-media, DRAM, memory-module, correctable, and
uncorrectable error injection. Poison start addresses are 64-byte aligned and
lengths are multiples of 64 bytes.

Sources:

- [QEMU CXL system documentation](https://www.qemu.org/docs/master/system/devices/cxl.html)
- [QEMU QMP command index](https://www.qemu.org/docs/master/qapi-qmp-index.html)
- [QEMU CXL QAPI schema](https://gitlab.com/qemu-project/qemu/-/blob/master/qapi/cxl.json)

### Driver isolation prior art

Fuchsia runs drivers in driver-host processes. A host isolates its contained
drivers from other processes, but may contain more than one driver. The
`colocate` request is advisory and defaults false. Therefore SimpleOS may use
Fuchsia as precedent for isolated-by-default hosts plus controlled colocation,
but must not claim Fuchsia guarantees exactly one process per driver.

Sources:

- [Fuchsia Driver Framework](https://fuchsia.dev/fuchsia-src/concepts/drivers/driver_framework)
- [Fuchsia driver runner and colocation](https://fuchsia.dev/fuchsia-src/concepts/components/v2/driver_runner)

seL4 and the seL4 Device Driver Framework support user-level, isolated,
single-purpose components with low-overhead asynchronous/zero-copy transport.
This supports the control-plane/data-plane split, while SimpleOS must still
define its own driver lifecycle and resource objects.

Sources:

- [seL4 FAQ](https://sel4.systems/About/FAQ.html)
- [seL4 Summit 2023 sDDF material](https://sel4.systems/Summit/2023/abstracts2023.html)

### Safe user-space DMA

Linux IOMMUFD exposes explicit IO address-space, device, hardware page-table,
and fault objects. An IOAS maps user memory to IOVAs; binding establishes device
DMA ownership. VFIO similarly relies on an IOMMU-protected boundary for secure
user-space device access. SimpleOS should copy the object/ownership lesson, not
the Linux API surface.

Sources:

- [Linux IOMMUFD userspace API](https://docs.kernel.org/userspace-api/iommufd.html)
- [Linux VFIO driver API](https://docs.kernel.org/driver-api/vfio.html)

Without a usable IOMMU, SimpleOS must report `dma_brokered`, use bounded bounce
buffers through a trusted broker, and deny unrestricted application
passthrough. It must not report `iommu_isolated`.

### USB HID and audio

USB HID remains self-describing through report descriptors. HID class 1.11 and
HID Usage Tables 1.7 (January 27, 2026) support a generic parser rather than
fixed boot keyboard/mouse assumptions.

Source: [USB-IF HID documents](https://www.usb.org/hid)

USB Audio Device Class 4.0 was released on October 31, 2025. SimpleOS should
keep version parsing separate from a stable `AudioEndpoint` protocol and begin
with a QEMU/common-hardware UAC 1/2 subset.

Source: [USB Audio Devices Release 4.0](https://www.usb.org/document-library/usb-audio-devices-release-40-and-adopters-agreement)

Intel documents HDA DMA streams, memory-based command/response transport, MSI,
codec links, and optional DSP capabilities. Splitting controller, codec, and
`audiod` policy is a SimpleOS design decision supported by these boundaries;
it is not mandated by Intel.

Source: [Intel HD Audio controller capabilities](https://edc.intel.com/content/www/us/en/design/products/platforms/processor-and-core-i3-n-series-datasheet-volume-1-of-2/intel-high-definition-audio-intel-hd-audio-controller-capabilities/)

### UNO Q

Arduino documents the UNO Q as a QRB2210 application processor with four
Cortex-A53 cores and Adreno GPU plus an STM32U585 Cortex-M33. It documents USB-C
role switching, powered-dongle keyboard/mouse/microphone/headphone use, JMISC
audio, and an MPU-MCU Bridge/RPC facility. Published interfaces do not document
CXL.

Sources:

- [Arduino UNO Q product documentation](https://docs.arduino.cc/hardware/uno-q)
- [Arduino UNO Q datasheet](https://docs.arduino.cc/resources/datasheets/ABX00162-datasheet.pdf)

Therefore `NoCxl` is the correct SimpleOS board policy based on documented
interfaces, but the research must say “no documented CXL interface,” not claim
proof about every internal QRB2210 capability. Native SimpleOS support also
requires independent boot, DT, GIC, timer, SMMU, clocks/reset, USB, storage,
audio, and physical evidence.

## Design constraints derived from the research

1. CXL support is a capability vector and revision, never one boolean.
2. Type 3 memory is the first QEMU target; it is not device-local execution.
3. Name a Type 3 host queue `CxlHostMapped`; reserve
   `CxlDeviceCoherent` for a proved device consumer.
4. Control-plane recovery must remain outside the CXL memory being recovered.
5. Driver isolation claims require distinct address spaces plus enforceable
   MMIO, IRQ, DMA/IOMMU, reset, and revocation evidence.
6. QEMU gates functional topology and fault behavior only.
7. Physical UNO Q, real CXL, Type 1/2, and device-resident rows remain blocked
   until target-specific prerequisites and resume commands exist.
