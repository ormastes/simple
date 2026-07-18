# DirectX Native Device Readback Evidence

- status: unavailable
- reason: directx-native-readback-requires-windows-win32-real
- source: not_device_readback
- backend handle: 0
- expected checksum: 0
- actual checksum: -1
- inner harness/Cargo exit code: missing
- wrapper gate status: unavailable
- wrapper exit code: 1
- timed out: false
- host os: Linux
- harness: build/directx/native_readback_probe.exe

## Required Native Path

ID3D11Texture2D render target -> staging texture -> CopyResource -> Map -> checksum -> Unmap.

## Raw Evidence

- directx_native_readback_status=unavailable
- directx_native_readback_reason=directx-native-readback-requires-windows-win32-real
- directx_native_readback_source=not_device_readback
- directx_native_readback_backend_handle=0
- directx_native_readback_expected_checksum=0
- directx_native_readback_actual_checksum=-1
- directx_native_readback_exit_code=missing
- directx_native_readback_timed_out=false
- directx_native_readback_host_os=Linux
- directx_native_readback_harness=build/directx/native_readback_probe.exe
- directx_native_readback_timeout_seconds=180
- directx_native_readback_required_path=ID3D11Texture2D render target -> staging texture -> CopyResource -> Map -> checksum -> Unmap
- directx_native_readback_wrapper_gate_status=unavailable
- directx_native_readback_wrapper_exit_code=1
- directx_native_readback_report=doc/09_report/directx_native_readback_2026-06-16.md

## Windows Host Validation Checklist

- Host requirement: Windows host with `win32-real` runtime surface and `d3d11` availability.
- Run probe with explicit `win32-real` path:
  - `cargo run --manifest-path src/runtime/hosted/Cargo.toml --features win32-real --example directx_native_readback_probe`
- Run wrapper with same timeout model:
  - `sh scripts/check/check-directx-native-readback.shs`
  - Optional: `SIMPLE_DIRECTX_NATIVE_TIMEOUT_SECS=180 sh scripts/check/check-directx-native-readback.shs`
- CI entrypoint:
  - `.github/workflows/directx-windows-validation.yml`
  - `gh workflow run directx-windows-validation.yml --ref main`
