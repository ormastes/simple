# CUDA packed aggregate alignment is absent from MIR metadata

Status: open, source audit only; runtime reproduction UNRUN. Severity: P2.

Both CUDA backends derive aggregate alignment from natural field alignment.
MirTypeDef has no aggregate alignment field. Therefore packed fields small:u8
at0 and wide:u64 at1 have maximum end9, but cuda_struct_align returns8 and
cuda_struct_size rounds to16. Existing layout producer correctly reports
packed size9/alignment1. The current field-identity repair does not transport
that alignment and must not claim full packed CUDA support.

Follow-up: transport authoritative aggregate size/alignment or reject this
profile explicitly, with actual packed aggregate allocation/array-stride tests
through both admitted CUDA consumers. Do not add another layout algorithm.

## Resolution 2026-11-26 (verified on NVIDIA GB10)

Chosen branch: transport alignment, then reject. A probe on the GB10 showed
`st.global.u64 [base+1]` traps with `CUDA_ERROR_MISALIGNED_ADDRESS` (716), and
neither backend has byte-wise field lowering, so a packed aggregate cannot be
supported by fixing the size alone. `MirTypeDef.alignment` now carries
`TypeLayout.align` from the struct and class lowerers; `cuda_struct_admitted`
in both CUDA backends rejects any aggregate whose transported alignment is not
CUDA's natural one, from `cuda_type_size` and `field_layout`.

Evidence: `test/02_integration/gpu/cuda_packed_aggregate_live_spec.spl` (plugin)
and `cuda_packed_aggregate_legacy_live_spec.spl` (legacy). At origin both
compiled the packed type and the device wrote at stride 16 against the host's 9
(61 mismatches); now both reject it, and the naturally aligned control runs with
0 device mismatches.

Residual gap: alignment 0 means "not transported" and falls back to natural.
MIR rebuilt by the loop-shape projection, or read back from an SMF
`runtime_std` frame, has 0, because the identity text and the SMF frame were
deliberately left unchanged.
