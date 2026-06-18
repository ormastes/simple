# HTML/CSS Vulkan RenderDoc Probe - 2026-06-17

## Scope

Probe for the requested generated HTML/CSS Vulkan IO-level evidence path:
Chrome/Chromium with Vulkan enabled, captured through RenderDoc CLI.

## Current Host

- `vulkaninfo --summary` is available.
- Vulkan devices are present:
  - NVIDIA TITAN RTX, NVIDIA proprietary driver `580.126.16`
  - NVIDIA RTX A6000, NVIDIA proprietary driver `580.126.16`
  - llvmpipe CPU fallback
- Vulkan instance layer list includes `VK_LAYER_RENDERDOC_Capture`.
- User-local Chrome is available:
  `/home/ormastes/.cache/ms-playwright/chromium-1223/chrome-linux64/chrome`
  (`Google Chrome for Testing 148.0.7778.96`).
- Official RenderDoc stable `v1.44` Linux x64 tarball was downloaded from
  `https://renderdoc.org/stable/1.44/renderdoc_1.44.tar.gz` and extracted under
  `build/tools/renderdoc-1.44/`.
- `build/tools/renderdoc-1.44/bin/renderdoccmd` reports
  `renderdoccmd x64 v1.44`.
- `renderdoccmd vulkanlayer --register --user` completed and
  `renderdoccmd vulkanlayer --explain` reports the Vulkan layer is correctly
  registered.

## Missing Runtime Tools

- `renderdoccmd`: missing from `PATH` and common `/usr`, `/opt`, and home paths.
- `qrenderdoc`: missing from `PATH` and common `/usr`, `/opt`, and home paths.
- `google-chrome`, `chromium`, and `chromium-browser`: missing from `PATH`.
- `apt-cache search renderdoc`: no package from configured apt sources.
- `snap info chromium`: Chromium is available as a snap.
- `snap info renderdoc`: no RenderDoc package metadata returned.
- `snap install chromium`: failed with `access denied`.
- `sudo -n snap install chromium`: failed because a password is required.

## Simple2D / Engine2D Vulkan Readback

Command:

```sh
sh scripts/check/check-vulkan-engine2d-readback.shs
```

Result:

- `backend_name=vulkan`
- `present_exercised=true`
- `readback_exercised=true`
- `clear_mismatches=0`
- `rect_mismatches=0`
- `overall=pass`
- `report_path=doc/09_report/vulkan_engine2d_readback_2026-06-17.md`

This closes the Simple2D-backed Vulkan local readback portion for this host.

## Chrome Vulkan RenderDoc Attempts

Fixture:

- `test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html`

RenderDoc/Chrome command shape:

```sh
xvfb-run -a build/tools/renderdoc-1.44/bin/renderdoccmd capture \
  -w -c build/renderdoc/html_css/generated_gui_capture \
  /home/ormastes/.cache/ms-playwright/chromium-1223/chrome-linux64/chrome \
  --headless=new --no-sandbox --disable-dev-shm-usage \
  --enable-features=Vulkan,DefaultANGLEVulkan,VulkanFromANGLE \
  --use-angle=vulkan --enable-unsafe-webgpu --disable-software-rasterizer \
  --window-size=800,600 --run-all-compositor-stages-before-draw \
  --virtual-time-budget=1000 \
  --screenshot=/home/ormastes/dev/pub/simple/build/renderdoc/html_css/generated_gui.png \
  file:///home/ormastes/dev/pub/simple/test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html
```

Attempt results:

- Windowed Chrome under RenderDoc timed out after 90 seconds and emitted no
  capture.
- Headless Chrome under RenderDoc exited and wrote
  `build/renderdoc/html_css/generated_gui.png`, but the GPU process segfaulted
  repeatedly with `exit_code=139`; no `.rdc` capture was emitted.
- Headless Chrome under RenderDoc with `--opt-hook-children` failed earlier:
  GPU process launch failed with `error_code=1002`, then Chrome aborted with
  `GPU process isn't usable`; no `.rdc` capture was emitted.
- Headless Chrome under RenderDoc with `--opt-hook-children` and
  `--disable-gpu-sandbox` still failed: the GPU process repeatedly crashed with
  `exit_code=139`; the stack trace included
  `build/tools/renderdoc-1.44/lib/librenderdoc.so`, and the command timed out
  without emitting an `.rdc`.
- Headless Chrome under RenderDoc with `--in-process-gpu` and
  `--disable-gpu-sandbox` also failed: Chrome segfaulted immediately and emitted
  no `.rdc`.
- `find build/renderdoc/html_css -maxdepth 1 -type f` shows PNG screenshot
  output only, not a RenderDoc capture.

## Docker GPU RenderDoc Attempt

Host/container prerequisites checked:

- Docker is available to the current user.
- `docker run --rm --gpus all nvidia/cuda:12.4.1-base-ubuntu22.04 nvidia-smi`
  sees both NVIDIA GPUs.
- The Playwright container image
  `mcr.microsoft.com/playwright:v1.57.0-noble` sees `/dev/dri` and the NVIDIA
  GPUs when launched with `--gpus all --device /dev/dri`.
- The container bundled Chromium is
  `/ms-playwright/chromium-1200/chrome-linux64/chrome`.

Container command shape:

```sh
docker run --rm --gpus all --device /dev/dri --ipc=host \
  --security-opt seccomp=unconfined --cap-add SYS_PTRACE \
  -v "$PWD":/work -v "$PWD/build/tools/renderdoc-1.44":/renderdoc -w /work \
  mcr.microsoft.com/playwright:v1.57.0-noble \
  bash -lc 'xvfb-run -a /renderdoc/bin/renderdoccmd capture --opt-hook-children \
    -w -c /work/build/renderdoc/html_css_container/generated_gui_container \
    /ms-playwright/chromium-1200/chrome-linux64/chrome \
    --no-sandbox --disable-dev-shm-usage --disable-gpu-sandbox \
    --enable-features=Vulkan,DefaultANGLEVulkan,VulkanFromANGLE \
    --use-angle=vulkan --enable-unsafe-webgpu --disable-software-rasterizer \
    --window-size=800,600 --run-all-compositor-stages-before-draw \
    --virtual-time-budget=1000 \
    --screenshot=/work/build/renderdoc/html_css_container/generated_gui_container.png \
    file:///work/test/fixtures/html_css/generated_gui_vulkan_renderdoc_fixture.html'
```

Result:

- Chromium launched under containerized RenderDoc.
- The GPU process repeatedly crashed with `exit_code=139`.
- The stack trace included `/renderdoc/lib/librenderdoc.so`.
- `build/renderdoc/html_css_container/` contained no emitted `.rdc` or
  screenshot artifact after the timed run.

This confirms that a Docker GPU container is available on the host, but it does
not avoid the Chrome GPU-process crash under RenderDoc/Vulkan.

## QEMU GPU Attempts

Physical GPU passthrough discovery:

- Host kernel command line includes `amd_iommu=on iommu=pt`.
- Both NVIDIA GPUs report `display_active=Disabled`.
- No active NVIDIA compute processes were reported by `nvidia-smi`.
- TITAN RTX PCI functions:
  - `42:00.0` VGA `[10de:1e02]`
  - `42:00.1` audio `[10de:10f7]`
  - `42:00.2` USB `[10de:1ad6]`
  - `42:00.3` UCSI `[10de:1ad7]`
- All TITAN RTX functions are isolated together in IOMMU group 26.
- RTX A6000 VGA/audio are isolated together in IOMMU group 16.

Direct physical passthrough probe:

```sh
qemu-system-x86_64 -nodefaults -machine q35,accel=kvm -m 1024 \
  -display none -serial stdio \
  -device vfio-pci,host=42:00.0,multifunction=on \
  -device vfio-pci,host=42:00.1 \
  -device vfio-pci,host=42:00.2 \
  -device vfio-pci,host=42:00.3
```

Result:

- QEMU failed before VM startup:
  `failed to open /dev/vfio/26: No such file or directory`.
- `/dev/vfio/26` is absent because the TITAN RTX group is still bound to host
  drivers, not `vfio-pci`.
- The current session does not have passwordless sudo, so it cannot safely
  detach/rebind the GPU group to `vfio-pci`.

Virtual GPU / QEMU EGL route:

- Host QEMU supports `egl-headless` and `virtio-vga-gl`, but host execution
  failed with `egl: no drm render node available`.
- A disposable Docker container launched with `--gpus all --device /dev/dri
  --device /dev/kvm` can run QEMU with:

```sh
qemu-system-x86_64 -nodefaults -machine q35,accel=kvm -m 512 \
  -display egl-headless,gl=on -device virtio-vga-gl
```

- After adding QEMU/EGL/Mesa packages in the container, this command ran until
  its timeout, proving the Docker+QEMU EGL backend can initialize.
- A reusable local Docker image `simple-qemu-egl-probe` was built for repeated
  probes.
- The existing Ubuntu server overlay
  `build/qemu/html_css_renderdoc/ubuntu-overlay.qcow2` booted under
  Docker+QEMU+`virtio-vga-gl` for the bounded run, but emitted no serial output
  and did not open the forwarded SSH port `2229`.

This leaves two viable next paths:

- privileged VFIO setup for the isolated TITAN RTX group, then a desktop guest
  with NVIDIA driver, Chrome, and RenderDoc;
- prepare or install a reachable Linux guest for the already-working
  Docker+QEMU+`virtio-vga-gl` route, then validate whether guest Chrome can use
  Vulkan/RenderDoc through the virtual GPU stack.

## Seeded QEMU Guest Access Attempt

Follow-up on 2026-06-18:

- Added a throwaway NoCloud seed under
  `build/qemu/html_css_renderdoc/seed-user-data` and
  `build/qemu/html_css_renderdoc/seed-meta-data`.
- Generated `build/qemu/html_css_renderdoc/seed.iso` with `genisoimage`.
- Booted the existing overlay through the working Docker+QEMU EGL route:

```sh
docker run --rm --name simple-html-css-qemu-probe --gpus all --device /dev/dri \
  --device /dev/kvm --ipc=host -p 127.0.0.1:2229:2229 \
  -v "$PWD":/work \
  -v /home/ormastes/dev/pri/llm_storage:/home/ormastes/dev/pri/llm_storage:ro \
  -w /work simple-qemu-egl-probe bash -lc \
  'qemu-system-x86_64 -machine q35,accel=kvm -cpu host -smp 4 -m 4096 \
    -display egl-headless,gl=on -device virtio-vga-gl \
    -drive if=virtio,file=/work/build/qemu/html_css_renderdoc/ubuntu-overlay.qcow2,format=qcow2 \
    -drive if=virtio,format=raw,readonly=on,file=/work/build/qemu/html_css_renderdoc/seed.iso \
    -netdev user,id=n0,hostfwd=tcp::2229-:22 -device virtio-net-pci,netdev=n0 \
    -serial mon:stdio'
```

Result:

- The forwarded TCP port opened immediately.
- SSH never completed banner exchange across the bounded retry window.
- QEMU console output only reported repeated NVIDIA PCI-id probe lines from the
  EGL stack, not guest boot or cloud-init progress.
- The Docker/QEMU process was stopped and no probe processes remained.

This proves the previous missing-seed issue is not the only blocker. The
existing Ubuntu qcow2 still does not provide a usable guest session through this
headless EGL boot path, so it cannot yet be used for in-guest Chrome,
Vulkan, or RenderDoc capture.

## QEMU NVMe Disk-Bus Probe

Follow-up on 2026-06-18:

- The base image is named `ubuntu_server_24.10_nvme_qemu.qcow2`, so the earlier
  virtio-disk boot may have mismatched the image's expected device model.
- Retried the same Docker+QEMU EGL route with the overlay attached as an
  emulated NVMe device:

```sh
qemu-system-x86_64 -machine q35,accel=kvm -cpu host -smp 4 -m 4096 \
  -display egl-headless,gl=on -device virtio-vga-gl \
  -drive if=none,id=nvme0,file=/work/build/qemu/html_css_renderdoc/ubuntu-overlay.qcow2,format=qcow2 \
  -device nvme,drive=nvme0,serial=htmlcssrenderdoc \
  -drive if=virtio,format=raw,readonly=on,file=/work/build/qemu/html_css_renderdoc/seed.iso \
  -netdev user,id=n0,hostfwd=tcp::2230-:22 -device virtio-net-pci,netdev=n0 \
  -serial mon:stdio
```

Result:

- The forwarded TCP port opened immediately.
- SSH again timed out during banner exchange for the bounded retry window.
- The QEMU process was stopped, and no QEMU or SSH probe processes remained.

The failure is therefore not explained solely by using a virtio disk for an
NVMe-named image. The current qcow2 remains unusable for the in-guest
Chrome/Vulkan/RenderDoc path without a working console, a different boot image,
or operator-provided guest credentials/boot requirements.

## Verdict

Local SSpec renderer coverage and Simple2D-backed Vulkan readback pass on this
host. RenderDoc CLI is now installed user-locally and registered, Chrome is
available through the Playwright cache, Docker GPU access works, and
Docker+QEMU can initialize an EGL-backed virtual GPU. The remaining blocker is a
working Chrome+Vulkan+RenderDoc environment: host and Docker Chromium attempts
crash under RenderDoc, direct VFIO passthrough needs privileged GPU rebind, and
the existing Ubuntu server qcow2 still does not expose a usable SSH guest
session even with a NoCloud seed attached and with the disk presented as NVMe.

This report does not close the Vulkan IO-level evidence request. It records the
current host prerequisite state for the next attempt.

## Fresh Guest and Shared RenderDoc Infrastructure

Follow-up on 2026-06-18:

- Built a fresh Ubuntu 24.04 guest rootfs with SSH, Vulkan tools, Mesa drivers,
  Xvfb/Openbox, and Chrome dependencies.
- Booted it with Docker+QEMU `virtio-vga-gl`; after enabling
  `systemd-networkd`, SSH was reachable and `/dev/dri/renderD128` existed.
- `vulkaninfo --summary` in the guest reported only `llvmpipe` CPU Vulkan.
- QEMU accepted `virtio-vga-gl` but did not support a `venus=true` property, so
  the guest could not expose Vulkan-over-virtio for non-CPU Vulkan evidence.
- RenderDoc v1.44 and Chrome 148 copied into the guest ran, and the RenderDoc
  Vulkan layer registered.
- `renderdoccmd capture` around Chrome reproduced the GPU-process segfault
  through `librenderdoc.so`; no `.rdc` was emitted.
- `--in-process-gpu` also segfaulted immediately and emitted no `.rdc`.

Infrastructure added after these probes:

- `scripts/tool/renderdoc-evidence.shs` is the canonical CLI for both capture
  styles.
- `capture-simple` owns the Simple in-application `rt_renderdoc_*` Engine2D
  Vulkan path.
- `capture-html` owns the original RenderDoc+Chrome HTML/CSS path.
- `scripts/setup/setup-renderdoc-env.shs` owns RenderDoc/Chrome path discovery
  and Vulkan layer registration.
- `test/helpers/renderdoc_capture_helper.shs` gives tests the same interface as
  the CLI.

This removes duplicate command setup. It does not close the Chrome-on-Vulkan
`.rdc` requirement on this host because the only reachable VM path exposes CPU
Vulkan and the Chrome+RenderDoc hook still crashes before a capture is written.

## Canonical CLI Capture Results

Follow-up on 2026-06-18:

Simple in-application RenderDoc capture:

```sh
RDOC_OUTPUT_DIR=build/renderdoc/canonical-probe \
  timeout 240s scripts/tool/renderdoc-evidence.shs capture-simple
```

Result:

- `build/renderdoc/canonical-probe/simple/evidence.env`
- `rdoc_backend=simple`
- `rdoc_scene=vulkan-engine2d`
- `rdoc_capture_status=pass`
- `rdoc_capture_reason=pass`
- `rdoc_capture_file=build/renderdoc/canonical-probe/simple/simple_gui_capture.rdc`
- `rdoc_capture_magic=RDOC`

Original RenderDoc + Chrome HTML/CSS capture:

```sh
RDOC_OUTPUT_DIR=build/renderdoc/canonical-probe \
  RDOC_CAPTURE_TIMEOUT_SECS=45 \
  timeout 70s scripts/tool/renderdoc-evidence.shs capture-html
```

Result:

- `build/renderdoc/canonical-probe/html/evidence.env`
- `rdoc_backend=original`
- `rdoc_scene=html-css-chrome`
- `rdoc_capture_status=fail`
- `rdoc_capture_reason=missing-rdc`
- Chrome GPU subprocesses segfaulted with stacks through
  `build/tools/renderdoc/lib/librenderdoc.so`.
- No `.rdc` file was emitted.

This closes the local Simple RenderDoc/Engine2D Vulkan `.rdc` evidence path.
The original Chrome-on-Vulkan HTML/CSS RenderDoc requirement remains blocked on
this host by the RenderDoc/Chrome GPU-process crash.

An external host can close the remaining gate by producing original
RenderDoc+Chrome evidence and running:

```sh
RDOC_HTML_EVIDENCE_ENV=<path-to-original-chrome-renderdoc-evidence.env> \
  sh scripts/check/check-renderdoc-html-external-host-gate.shs
```

The gate writes `rdoc_html_external_gate_status=pass` only when the source
evidence reports `rdoc_backend=original`, `rdoc_capture_status=pass`,
`rdoc_capture_magic=RDOC`, and an existing `.rdc` file.

## macOS Portability Follow-Up

macOS can be used for supplemental portability evidence, but it does not replace
the remaining original Chrome-on-Linux-Vulkan RenderDoc gate. The expected macOS
Vulkan path is Metal-backed portability, typically MoltenVK from the LunarG
Vulkan SDK. That is useful for checking whether the Simple Vulkan capture path
runs through Vulkan-over-Metal, but it is not the same GPU/driver path as the
blocked Linux Chrome/Vulkan capture.

Use the shared infrastructure on a macOS host where possible:

```sh
scripts/setup/setup-renderdoc-env.shs --check
scripts/tool/renderdoc-evidence.shs capture-simple
scripts/tool/renderdoc-evidence.shs capture-html
```

Record the result as a new `doc/09_report/` entry with macOS version, CPU
architecture, GPU model, Vulkan SDK/MoltenVK version, RenderDoc availability,
capture status, and whether Chrome used Vulkan-over-Metal, direct Metal, or no
GPU path. If RenderDoc cannot capture the Metal-backed path, use Xcode GPU Frame
Capture as supplemental Metal-level evidence and keep the external-host
RenderDoc gate fail-closed.
