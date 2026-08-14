# Feature Expert — Render 8K80 CUDA/Vulkan campaign

## Scope

Own the A4–A8 readiness and evidence contract for 7680x4320 at 80 Hz. CUDA and
Vulkan may use the same NVIDIA device inside one container, but they are
separate APIs and separate evidence lanes.

## Canonical runner

```sh
sh scripts/setup/prepare-render-perf-8k80-container.shs --check-contract
sh scripts/setup/prepare-render-perf-8k80-container.shs --build \
  --base-image nvidia/cuda:<devel-tag>@sha256:<approved-digest> \
  --tag simple-render-8k80-nvidia:local \
  --receipt "$PWD/build/render_perf/8k80-container-image.env"
sh scripts/setup/prepare-render-perf-8k80-container.shs --check-gpu \
  simple-render-8k80-nvidia:local --gpu all
sh scripts/check/check-render-perf-8k80-container.shs --self-test
sh scripts/check/check-render-perf-8k80-container.shs --run \
  --compiler /absolute/path/to/bin/release/<triple>/simple \
  --compiler-provenance /absolute/path/to/compiler-provenance.env \
  --container-image <image@sha256-or-local-id> --gpu all
```

The base must be an NVIDIA CUDA devel image pinned by digest. The dedicated
Dockerfile uses a dated Ubuntu snapshot, installs `vulkan-tools` and
`/usr/bin/time`, rejects `mesa-vulkan-drivers`, and records Docker's immutable
image ID. NVIDIA Container Toolkit must inject the NVIDIA Vulkan ICD. The
runner requests `NVIDIA_DRIVER_CAPABILITIES=compute,utility,graphics`, disables
networking, drops capabilities, bounds CPU/RSS, and retains the image identity,
CUDA/Vulkan inventory, build logs, executable hashes, and API receipts.

## Evidence boundaries

- A4 is deliberately CPU DrawIR; GPU availability does not change it.
- CUDA qualification requires an actual generated kernel submit and exact
  device readback. It is environment evidence, not A5 rendering evidence.
- A5 requires the native strict semantic producer to select Vulkan, submit and
  fence 62 frames, perform device-origin readback outside timing, change the
  semantic revision/checksum, and use no fallback.
- `vulkaninfo` and `nvidia-smi` are retained inventory only.
- Headless CUDA/Vulkan proves device execution, never physical 8K80 scanout.
- A6/A8 require an EDID-bearing active 7680x4320 mode at 80 Hz or faster plus
  independently captured/read-back correlated scanout.

## Tests and documentation

- Modern readiness SSpec:
  `test/03_system/gui/wm_compare/render_8k80_cuda_vulkan_container_readiness_spec.spl`
- Semantic producer SSpec:
  `test/03_system/gui/wm_compare/strict_semantic_vulkan_producer_spec.spl`
- Visible-window SSpec:
  `test/03_system/gui/wm_compare/strict_semantic_vulkan_window_producer_spec.spl`
- Shell contract:
  `test/05_perf/profile_scripts/render_perf_8k80_container_contract_test.shs`
- Image contract:
  `test/05_perf/profile_scripts/render_perf_8k80_container_image_contract_test.shs`
- Operator guide: `doc/07_guide/app/ui/render_8k80_nvidia_container.md`

Unavailable prerequisites are `blocked`, invalid evidence is `failed`, and the
campaign remains `blocked-physical` until fresh correlated A6/A8 evidence exists.
