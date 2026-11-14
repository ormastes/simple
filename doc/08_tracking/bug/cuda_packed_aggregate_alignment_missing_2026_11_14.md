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
