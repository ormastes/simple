# 📦 Module 59.6: Dynamic NVMe Loading Matrix

**Goal**: Track the officially supported NVMe loading strategies and connect them to PyTorch dispatcher checks so the runtime can validate when dynamic loading is enabled.

## Highlights

- Builds on the dispatcher matrix from Module 59.5.
- Enumerates ALL_IN_MEMORY, DYNAMIC_FFN_ONLY, and DYNAMIC_ALL.
- CLI emits mode metadata and verifies GPU writes through `nvme_kernel.cu`.

## Build / Test

```bash
cmake -B build -S . -G Ninja
ninja -C build 59_6_Dynamic_NVMe_Loading_cli 59_6_Dynamic_NVMe_Loading_unit_common
./build/50.GPU-NVMe_Interaction/59.Attention_Expert_Dynamic_Load/59.6_Dynamic_NVMe_Loading/59_6_Dynamic_NVMe_Loading_cli
ctest -C Debug -R 59_6_Dynamic_NVMe_Loading_unit_common --output-on-failure
```

**Next module**: [`../59.7_Performance/`](../59.7_Performance/)
