<!-- codex-research -->
# Simple Platform Unification: Domain Research

**Date:** 2026-09-13

## Findings

### Host and target separation

LLVM cross-compilation distinguishes the system where a compiler runs from the
target triple and sysroot used to produce code. This supports three explicit
Simple dimensions: host execution environment, target code-generation profile,
and optional execution domain. A default host triple may seed configuration, but
must never silently overwrite an explicit SimpleOS target.

Source: [LLVM cross-compilation documentation](https://llvm.org/docs/HowToCrossCompileLLVM.html)

### QEMU is a selectable execution backend

QEMU exposes multiple accelerators depending on target and host, including KVM,
HVF, WHPX, and TCG. Consequently `accelerator: auto` must be resolved by a host
adapter into a receipt-bearing launch plan. TCG is the portable fallback; an
accelerator name is not a guest architectural property.

Source: [QEMU documentation](https://qemu.readthedocs.io/_/downloads/en/v8.1.5/pdf/)

### Firmware policy is outside the OS platform contract

UEFI defines firmware boot-manager policy that selects and loads UEFI images.
SimpleOS should consume a firmware/boot profile in its image and machine
manifests while keeping loader, SOSIX, and kernel contracts independent of the
development runner. Release evidence should identify the exact firmware path.

Source: [UEFI 2.11 Boot Manager](https://uefi.org/specs/UEFI/2.11/03_Boot_Manager.html)

### GPU admission requires queried features

Vulkan subgroup support is reported through physical-device properties and
storage buffers have explicit descriptor and memory semantics. A GPU parser
provider therefore requires concrete queried capabilities, resource bounds,
queue/fence completion evidence, and synchronization-safe buffers. Device
presence alone is insufficient. Selection also needs measured end-to-end cost,
including transfer and completion, so small inputs stay on CPU paths.

Sources: [Vulkan subgroup guide](https://docs.vulkan.org/guide/latest/subgroups.html),
[Vulkan specification](https://registry.khronos.org/vulkan/specs/latest-ratified/pdf/vkspec.pdf)

## Architecture implications

- Canonical target tuples and sysroots participate in build/cache identities.
- `QemuLaunchPlanV1` records executable, accelerator, firmware, normalized
  devices, image digest, and host-discovery reasons.
- `SimpleOsImageManifestV1` is backend-neutral and can be consumed by QEMU,
  hardware deployment, or hosted simulation.
- GPU parser promotion requires semantic parity plus a workload crossover model;
  successful provider loading is only admission evidence.
- Cold-boot release validation must remain distinct from reusable development VM
  transport and state.

### Evidence binds behavior, not loadability

Format admission, successful loading, or reaching an entry point proves only
transport. Promoted providers must be strongly bound, execute the required
behavior, and emit identity-bound receipts. Generated weak fallbacks represent
capability absence for parser and SimpleOS provider evidence alike.
