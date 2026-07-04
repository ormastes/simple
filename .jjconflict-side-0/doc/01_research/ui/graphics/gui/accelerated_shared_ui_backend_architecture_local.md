<!-- codex-research -->
# Accelerated Shared UI Backend Architecture - Domain Research

Date: 2026-06-03

## UI Shells And Process Boundaries

Electron uses a multi-process model: a main process manages application
lifecycle and windows, renderer processes run web UI, and preload scripts form
the privileged bridge. The official process-model and sandbox docs describe IPC
as the required path for renderer-to-main privileged work. This supports a
Simple architecture where Electron is only a host adapter around a shared render
and input envelope.

Tauri uses platform webviews with a Rust core and message passing between
frontend and backend. Its webview-version docs also matter for parity because
the concrete webview differs by OS. This supports treating Tauri as a shell
adapter that must consume the same Simple render/input artifacts as Electron and
pure Simple web.

Node.js worker threads are useful for CPU-intensive JavaScript work but are not
the right abstraction for normal async I/O. A Simple NodeJS backend should use
workers only for renderer compute or reference benchmarking, not for every hot
request.

Sources:
- Electron process model: https://www.electronjs.org/docs/latest/tutorial/process-model
- Electron sandboxing: https://www.electronjs.org/docs/latest/tutorial/sandbox
- Electron performance: https://www.electronjs.org/docs/latest/tutorial/performance
- Tauri architecture: https://v2.tauri.app/concept/architecture/
- Tauri webview versions: https://v2.tauri.app/reference/webview-versions/
- Node.js worker threads: https://nodejs.org/api/worker_threads.html

## GPU And Portable Compute

CUDA stays the NVIDIA-specific high-performance lane. NVIDIA documents NVCC as
LLVM-based, and LLVM documents an NVPTX backend with GPU programming
conventions. This matches the current Simple Rust compiler GPU backend, which
generates NVPTX/PTX.

OpenCL is now specified through Khronos unified OpenCL 3.1 documents. The
official OpenCL registry describes OpenCL as an API, language, libraries, and
runtime for heterogeneous processors; it also documents the OpenCL SPIR-V
environment. This makes OpenCL the portable compute target for non-NVIDIA GPU
offload and for CPU/GPU vendors with ICD support.

Vulkan is an explicit low-level graphics and compute API and consumes SPIR-V
shader modules. SPIR-V is the common Khronos intermediate representation for
graphics shaders and compute kernels across Vulkan and OpenCL environments,
but each client API has its own validation rules and memory model. A Simple
SPIR-V emitter therefore needs target environment metadata, not just one generic
SPIR-V artifact.

Metal is Apple's graphics and compute API. It should remain a native Apple
backend using Metal shading language/metallib artifacts and platform-specific
profiling, while sharing the same Engine2D and generated-kernel dispatch
contracts.

Sources:
- Khronos OpenCL registry: https://registry.khronos.org/OpenCL/
- OpenCL unified specification: https://registry.khronos.org/OpenCL/specs/unified/html/OpenCL_Ext.html
- OpenCL SPIR-V environment: https://registry.khronos.org/OpenCL/specs/3.0-unified/html/OpenCL_Env.html
- Khronos SPIR-V registry: https://registry.khronos.org/SPIR-V/
- Vulkan specification: https://registry.khronos.org/vulkan/specs/latest/html/vkspec.html
- LLVM NVPTX backend: https://llvm.org/docs/NVPTXUsage.html
- NVIDIA CUDA LLVM compiler: https://developer.nvidia.com/cuda-llvm-compiler
- Apple Metal overview: https://developer.apple.com/metal/

## CPU SIMD

LLVM auto-vectorization documents loop and SLP vectorizers and exposes width
controls, while target backends such as RISC-V vector support scalable vectors.
Arm Neon is a fixed-width SIMD extension for Cortex-A/R workloads including UI
and graphics, while SVE/SVE2 is length-agnostic. Simple's CPU acceleration plan
should keep fixed-width x86/Neon and scalable RISC-V/SVE facts in optimization
provider metadata rather than hard-code one vector width.

Sources:
- LLVM vectorizers: https://llvm.org/docs/Vectorizers.html
- LLVM RISC-V vector extension: https://llvm.org/docs/RISCV/RISCVVectorExtension.html
- Arm Neon: https://www.arm.com/technologies/neon

## Architecture Implications

- Treat Electron, Tauri, NodeJS, browser, TUI, and pure Simple GUI as hosts for
  a shared semantic UI model plus backend-specific transport adapters.
- Treat Engine2D as the shared 2D backend interface for web renderer, WM,
  Simple GUI, and capture/equality.
- Treat CUDA as PTX/NVPTX and OpenCL/Vulkan as SPIR-V-family targets with
  separate target environment rules.
- Treat Metal as a native Apple target, not an OpenCL replacement.
- Require every accelerated claim to include selected backend, artifact format,
  device, feature flags, fallback reason, timing, RSS, binary size, and readback
  provenance.
