# Host QEMU `virtio-gpu-gl` cannot load — missing `qemu_egl_display` symbol (blocks B0/venus)

Date: 2026-08-11. Lane: V1 (board Vulkan B0/venus verification).

## Summary

On this host, `qemu-system-x86_64` (Debian 1:8.2.2+ds-0ubuntu1.17, from
`qemu-system-x86` + `qemu-system-modules-opengl`, both installed) cannot attach
`virtio-gpu-gl` / `virtio-gpu-gl-pci` to any machine. This is a QEMU packaging
defect on this host, not a venus-specific gap, and it blocks B0
(`doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md`) before
venus can even be evaluated.

## Evidence

```
$ qemu-system-x86_64 -device virtio-gpu-gl,help
qemu-system-x86_64: -device virtio-gpu-gl,help: failed to open module:
/usr/lib/x86_64-linux-gnu/qemu/hw-display-virtio-gpu-gl.so: undefined symbol:
qemu_egl_display

$ dpkg -l | grep -i virglrenderer
ii  libvirglrenderer1:amd64  1.0.0-1ubuntu2  amd64  virtual GPU for KVM virtualization

$ dpkg -L qemu-system-modules-opengl | grep '\.so$'
.../audio-dbus.so .../hw-display-virtio-gpu-gl.so .../hw-display-virtio-gpu-pci-gl.so
.../hw-display-virtio-vga-gl.so .../ui-dbus.so .../ui-egl-headless.so .../ui-opengl.so
# nm -D on every one of the 6 above: none exports `qemu_egl_display`.

$ nm -D /usr/bin/qemu-system-x86_64 | grep egl_display
# (empty — main binary does not export it either)

$ qemu-system-x86_64 -M q35 -display egl-headless -device virtio-gpu-gl -nographic
qemu-system-x86_64: -device virtio-gpu-gl: opengl is not available
```

`qemu_egl_display` is expected to be defined in the main `qemu-system-x86_64`
binary when QEMU is configured `--enable-opengl`; the hw-display module then
binds to it dynamically. On this Ubuntu 24.04 build the symbol is absent from
the main binary, so every `.so` that references it (all three `*-gl.so` device
modules) fails to load — with or without `-display egl-headless` forcing the UI
opengl module to init first, and regardless of `venus=on`.

## Impact

- B0 (venus/virtio-gpu, `qemu_only: true`) cannot be attempted at all on this
  host: `virtio-gpu-gl` cannot attach to any machine type, including the
  mandatory OVMF-pflash boot path (`.claude/rules/board-runnable.md`) — the
  device fails at realize time before machine type or firmware matters.
  Confirmed independent of venus: plain (non-venus) virgl 3D accel is equally
  broken here.
- This is **not** the "venus not supported by this virglrenderer" gap
  described elsewhere — it never gets far enough to reach virglrenderer/venus
  negotiation.

## Fix / workaround (not attempted — outside this lane's scope)

Needs a `qemu-system-x86_64` build actually compiled with working
`--enable-opengl` (verify via `nm -D <binary> | grep qemu_egl_display` before
trusting any future host), or building QEMU from source with venus support
explicitly enabled. Until then, B0 stays unreachable in this environment and
`board_runnable_count()` correctly stays 0 for it.

## Related

- `doc/01_research/os/vulkan/venus_virtio_gpu_protocol_facts.md` §9-10 (updated
  2026-08-11 with this evidence, replacing "unverified"/"reportedly" language).
- `doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md:68`
  ("reportedly fails to load") — should be updated by its owning lane to cite
  this measurement instead of hedging.

---

## Triage classification 2026-08-17 — DEFERRED: requires QEMU host GL stack

Reviewed in the second-pass backlog sweep. Not actionable from this session:
the missing EGL symbol is a property of the host's virtio-gpu/GL libraries, diagnosable only on a machine with that stack installed and a QEMU run. No code change is possible without that, so no
speculative fix was attempted. Classification recorded here so future sweeps
skip it in O(1) instead of re-deriving the blocker. Status remains OPEN.
