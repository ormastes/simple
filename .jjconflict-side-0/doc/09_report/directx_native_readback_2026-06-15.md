# DirectX Native Device Readback Evidence

- status: unavailable
- reason: directx-native-readback-requires-windows-win32-real
- source: not_device_readback
- backend handle: 0
- expected checksum: 2058049037
- actual checksum: -1
- inner harness/Cargo exit code: 0
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
- directx_native_readback_expected_checksum=2058049037
- directx_native_readback_actual_checksum=-1
- directx_native_readback_exit_code=0
- directx_native_readback_timed_out=false
- directx_native_readback_timeout_seconds=180
- directx_native_readback_harness=cargo-example:directx_native_readback_probe
- directx_native_readback_required_path=ID3D11Texture2D render target -> staging texture -> CopyResource -> Map -> checksum -> Unmap
- directx_native_readback_wrapper_gate_status=unavailable
- directx_native_readback_wrapper_exit_code=1
- directx_native_readback_report=doc/09_report/directx_native_readback_2026-06-15.md
