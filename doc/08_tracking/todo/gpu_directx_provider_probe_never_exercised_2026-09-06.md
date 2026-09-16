# TODO: [gpu][P2] Exercise the DirectX provider probe on a Windows or DXVK host

Date: 2026-09-06
Lane: GPU scheduler hardening (plan doc/03_plan/ui/gpu_scheduler_hardening_gpu_resident_rendering.md)
Rule: this may not be closed by a source scan, a routing receipt, or an interpreter run.

`directx` in this tree is D3D11 via DXVK; there is no D3D12 provider. The probe is never
executed on this macOS host and reports unavailable by construction.

Closing evidence: a probe transcript from a Windows or DXVK host showing the adapter identity
and the resulting grade, with the api level still reported as `d3d11-dxvk`, never d3d12.
