<!-- codex-research -->
# Domain research: headless GPU evidence versus physical 8K80

NVIDIA Container Toolkit exposes selected GPUs and driver capabilities to a
container; `compute` is needed for CUDA and `graphics` is needed for graphics
APIs. Device enumeration alone is inventory, not proof that a render workload
submitted, completed, and produced device-origin pixels. See NVIDIA's
container runtime documentation:
https://docs.nvidia.com/datacenter/cloud-native/container-toolkit/latest/docker-specialized.html

Vulkan distinguishes offscreen/headless rendering from display presentation.
`VK_EXT_headless_surface` can support presentation-like execution without a
physical display, while `VK_KHR_display` and platform WSI/EDID evidence address
display paths. Neither headless rendering nor CUDA compute proves connector
scanout. See the Khronos extension registry:
https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VK_EXT_headless_surface.html

Therefore the evidence model must keep three scopes distinct:

1. native CPU DrawIR execution (A4's existing contract),
2. strict device-origin Vulkan semantic rendering (A5 and software A7), and
3. physical connector/presentation evidence (A6/A8).

The parent receipt may correlate these scopes, but must never promote scope 1
or 2 into scope 3. The 80 Hz performance bound is p95 <=12,500,000 ns.
