# TLDR: SimpleOS GPU and Knowledge Routing

- Rendering uses `VulkanDevicePort`; compute uses `ProcessingDevicePort`.
- CUDA implements the processing port and retains CUDA identity.
- Adreno/Turnip implements the Vulkan port through staged board evidence.
- QEMU host-offload and guest-native Vulkan are distinct evidence classes.
- Venus protocol admission validates negotiation and bounded command layouts;
  it cannot claim submission, fence completion, readback, or guest-native PASS.
- SPipe loads feature-group plus layer-base knowledge deterministically.
- Kernel/drivers force MDSOC-only; services/apps may use MDSOC+.
- Native PASS requires device-origin readback and exact CPU-oracle parity.
- Direct Venus remains blocked on blob/context negotiation, guest ICD,
  shared-memory mapping, real submission/fence completion, and QEMU readback.
