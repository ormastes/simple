# Headless QEMU/Virgl Container Capability — 2026-08-26

## Verdict

`PASS` for host/container capability. Guest WM capture remains `UNCLAIMED`.

The digest-pinned Ubuntu 24.04 image starts QEMU 8.2.2 with KVM,
`egl-headless`, and `virtio-vga-gl` against `/dev/dri/renderD128`. The VM is
paused deliberately and survives until the bounded five-second timeout. The
container has no network, a read-only root filesystem, all capabilities
dropped, `no-new-privileges`, the host non-root UID/GID, and only `/dev/kvm`
plus the selected DRM render node.

## Retained identity

- image tag: `simple-qemu-virgl-headless:8.2.2-ubuntu24.04`
- image ID: `sha256:06e8f8eb62f7cde58653b6f82dfc9336b7b6a81f116e273bf90cc83d85b4bd29`
- base image: `ubuntu@sha256:4fbb8e6a8395de5a7550b33509421a2bafbc0aab6c06ba2cef9ebffbc7092d90`
- QEMU package: `1:8.2.2+ds-0ubuntu1.18`
- packaged `ui-opengl.so` SHA-256: `456898b5eca8f1e0995b4c1e44e9cae6bd1c6fd2dcbbcddc0ff45053b6180655`
- render node: `/dev/dri/renderD128` (NVIDIA `10de:2230`)

Ubuntu's QEMU module loader does not resolve `qemu_egl_display` when the
virtio-gpu-gl module is probed directly. The launcher therefore preloads the
exact packaged `ui-opengl.so`; the capability gate records its path and hash.
No ambient `LD_PRELOAD` is installed on the host.

## Commands and evidence

```sh
sh scripts/setup/build-headless-qemu-virgl-container.shs
sh scripts/check/check-headless-qemu-virgl-container.shs
sh test/01_unit/scripts/qemu_virgl_container_contract_test.shs
```

Observed fields:

```text
headless_qemu_virgl_status=pass
headless_qemu_virgl_reason=bounded-paused-vm-survived
headless_qemu_virgl_guest_capture=unclaimed
qemu virgl container contract: PASS
```

The live follow-up is intentionally separate:

```sh
SIMPLE_BIN=/path/to/admitted/stage4/simple \
  sh scripts/check/check-qemu-gtk-wm-capture-container.shs
```

That command must retain a live QMP screendump, exact scene/pixel validation,
container identity, and the admitted compiler identity before the headless WM
requirement can pass.
