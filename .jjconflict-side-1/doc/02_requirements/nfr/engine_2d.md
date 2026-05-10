# Engine2D QEMU Graphics Core NFR

NFR-E2D-QEMU-001: The x86_64 QEMU Engine2D fixtures shall boot and emit their paint-complete serial markers within 30 seconds on the standard local QEMU harness.

NFR-E2D-QEMU-002: QMP framebuffer capture shall contain nonzero nonblack pixels after the paint marker.

NFR-E2D-QEMU-003: Primitive verification shall use strict pixel assertions for the expected line, rectangle, circle, and background coordinates.

NFR-E2D-QEMU-004: Normal test runs shall not rewrite tracked visual baselines. Baseline refresh requires `UPDATE_BASELINE=1`.

NFR-E2D-QEMU-005: The freestanding graphics-core path shall not depend on host GPU backends, host windowing, CUDA, Vulkan, OpenGL, Metal, ROCm, Intel oneAPI, or runtime package assets.

NFR-E2D-QEMU-006: The guest shall remain alive after the paint marker until the harness stops QEMU, preventing QMP capture races.
