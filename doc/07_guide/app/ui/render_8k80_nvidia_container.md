# Preparing the NVIDIA 8K80 campaign image

The image preparation contract can be checked without GPU hardware:

```sh
sh scripts/setup/prepare-render-perf-8k80-container.shs --check-contract
sh test/05_perf/profile_scripts/render_perf_8k80_container_image_contract_test.shs
```

Build from an NVIDIA CUDA **devel** image pinned by digest (the CUDA
qualification compiles PTX with `nvcc`) and record the resulting immutable ID:

```sh
sh scripts/setup/prepare-render-perf-8k80-container.shs --build \
  --base-image nvidia/cuda:<approved-devel-tag>@sha256:<approved-digest> \
  --tag simple-render-8k80-nvidia:local \
  --receipt "$PWD/build/render_perf/8k80-container-image.env"
```

Do not install `mesa-vulkan-drivers` to make the check green. `vulkan-tools`
provides `vulkaninfo`; NVIDIA Container Toolkit injects the host NVIDIA Vulkan
ICD. Before the campaign, check injection on the selected GPU:

```sh
sh scripts/setup/prepare-render-perf-8k80-container.shs --check-gpu \
  simple-render-8k80-nvidia:local --gpu all
```

The live check requests `NVIDIA_DRIVER_CAPABILITIES=compute,utility,graphics`
and requires Vulkan inventory to name an NVIDIA device. This prepares A5; it
does not prove Vulkan submission, 8K80 performance, a physical 80 Hz mode, or
scanout capture. Those remain the campaign producer and physical gates.
Both non-live image inspection and live injection checks default to 4 GiB,
2 CPUs, and 256 processes. Override `CONTAINER_MEMORY`, `CONTAINER_CPUS`, or
`CONTAINER_PIDS_LIMIT` only when the retained campaign environment requires a
different explicit bound.

## A1 adapter-attribution system verification

The focused step-based contract is
`test/03_system/gui/wm_compare/render_8k80_a1_adapter_attribution_spec.spl`,
mirrored at
`doc/06_spec/03_system/gui/wm_compare/render_8k80_a1_adapter_attribution_spec.md`.
It traces REQ-R8KC-004/006 and NFR-R8KC-004/006 through three real scenarios:
the physical-wrapper identity self-test, the A1-versus-A6/A8 scope edge, and a
forced-unreachable-display blocker. The manual and test plan remain
`TEST_BLOCKED` until an admitted pure-Simple CLI can execute the spec, run
`sspec-maintain`, and regenerate the manual with `spipe-docgen`. Never use the
Rust bootstrap seed or a hand-maintained manual as runtime evidence.
