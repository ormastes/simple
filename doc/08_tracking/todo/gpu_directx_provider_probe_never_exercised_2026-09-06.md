# TODO: [gpu][P2] Exercise the DirectX provider probe on a Windows or DXVK host

Date: 2026-09-06
Lane: GPU scheduler hardening (plan doc/03_plan/ui/gpu_scheduler_hardening_gpu_resident_rendering.md)
Rule: this may not be closed by a source scan, a routing receipt, or an interpreter run.

`directx` in this tree is D3D11 via DXVK; there is no D3D12 provider. The probe is never
executed on this macOS host and reports unavailable by construction.

Closing evidence: a probe transcript from a Windows or DXVK host showing the adapter identity
and the resulting grade, with the api level still reported as `d3d11-dxvk`, never d3d12.

## 2026-09-16 — probe exercised on a Windows host (still open)

The probe was really executed on a Windows host (not a source scan) via
`SIMPLE_LIB=src bin/simple test <transcript spec> --mode=interpreter`, binary
`bin/release/x86_64-pc-windows-msvc/simple.exe`. Transcript (verbatim):

```
provider=directx
api_level=d3d11-dxvk
available=false
device_name=
device_type=
driver_identity=
distinct_phases=false
fence_token_available=false
device_timestamps_available=false
probe_error=no D3D11 hardware adapter reported on windows
```

The api level stays `d3d11-dxvk` as required, but no adapter identity is
reported, so per the closing rule this row stays OPEN. Root cause is not host
hardware: the deployed seed interpreter's
`rt_directx_hardware_adapter_identity_fn` is a hard stub returning 0
(`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs`); the only real
implementation lives in the C runtime (`src/runtime/runtime_directx_core.c`)
used by native builds, and the Rust runtime crate exposes no `rt_directx_*`
symbols to bind to. (Also observed: `simple run` on the same seed binary
segfaults exit 139 on this script; `test --mode=interpreter` is the working
path.)

Unblock paths, either:
1. wire the seed interpreter extern to the C runtime's real
   `rt_directx_hardware_adapter_identity()` (link + FFI), then re-run this
   transcript on any Windows host; or
2. run the transcript through a native-built binary on a Windows host with a
   visible D3D11 adapter (DXVK or hardware).
