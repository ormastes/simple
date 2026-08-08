# Local GPU Offload Break-Even Evidence

- host: Linux x86_64
- GPU: NVIDIA RTX A6000
- workload: 1920x1080 RGBA clear, 100 synchronized fill/CPU iterations;
  transfer is one full-frame sample
- build: `gcc -O2 -Wall -Wextra -Werror`
- policy: device work is preferred only at 1.5x CPU speedup

| Path | Device | CPU | Transfer | Classification |
|---|---:|---:|---:|---|
| CUDA PTX clear | 0.018 ms | 0.809 ms | none | preferred (45.8x) |
| CUDA PTX clear + device readback | 0.018 ms | 0.809 ms | 6.361 ms | available-not-preferred |
| Vulkan host-visible fill | 2.80 ms | 0.73 ms | none | available-not-preferred |
| Vulkan host-visible fill + full mapped readback | 2.80 ms | 0.73 ms | 99.041 ms | available-not-preferred |

The prior millisecond clock rounded short work toward zero, and the CPU
`memset` loops could be removed by `-O2` because their output was not consumed.
Both probes now use monotonic nanoseconds and call `memset` through a volatile
function pointer. Their hardware-free `--self-test` checks clock progress,
the measured fill, and exact even/odd 1.5x boundaries. CUDA launch/synchronize
status and Vulkan submit/wait status fail closed instead of producing timing
from rejected work.

This is host reference evidence only. TODO 570 remains open until the native
ProcessingIR daemon emits a fresh correlated CPU/device receipt.
