# CUDA/Vulkan interop and VUDA

- Phase: research; implementation is blocked on user option selection.
- Runtime need: same-device CUDA compute feeding Vulkan rendering without CPU
  readback, with explicit memory and synchronization provenance.
- Facades checked: Engine2D CUDA/Vulkan sessions, graphics-session policy,
  hosted runtime/SFFI, SimpleOS processing and Vulkan device ports.
- Safe available path: official Vulkan external-memory and external-semaphore
  interop. The May-2026 VUDA implementation is not published.
- Rejected shortcut: relabeling independent CUDA/Vulkan contexts, CPU copies,
  Venus host offload, or emulation as VUDA/spatial concurrency.
- Current host: Linux x86_64; NVIDIA RTX A6000 + TITAN RTX, driver 580.126.16,
  CUDA runtime libraries and Vulkan 1.4 NVIDIA driver present. No VUDA patches
  or capability receipt found.
- Preserved prior work: uncommitted pure PCI BAR resolver belongs to the prior
  SimpleOS Venus slice and must not be folded into this research commit.
