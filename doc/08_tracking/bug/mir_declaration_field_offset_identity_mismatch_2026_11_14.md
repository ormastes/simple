# MIR field offsets lose declaration identity after layout sorting

Status: source-reviewed checkpoint; runtime verification UNRUN.
Severity: P1. Owner: codex-mir-field-layout-20261114.

Source audit on release `c541817df822dd0d371371034ad79a6a44fd3e1c`:
`compute_struct_layout` defaults to stable descending-size physical ordering.
Both `lower_struct_type` and `lower_class_type` instead pair declaration
`fields[fi]` with physical `layout.fields[fi].offset`. For declared
`small: u8, wide: u64`, the physical rows are `wide@0, small@8`, but the MIR
metadata associates `small@0, wide@8`. CUDA field addressing trusts that metadata.

After correcting the association, CUDA's last-declaration-field sizing would
compute 8 instead of the required aligned maximum extent 16. Its extent must
use every existing offset plus that field's actual CUDA size, then the existing
alignment owner. Neither repair should recompute or duplicate field layout.

One authoritative `30.types` association helper validates exact unique field
identity and maps existing physical offsets into declaration order. Struct,
class and TargetHIR readers share it. Missing, duplicate or extra fields fail
before MIR type publication. Computed layout policy, offsets and alignment stay
owned by the existing target-aware layout producer.

Related `stage2_struct_field_offset_model_mismatch_oob_read_2026-08-30` reports
different cross-module layouts in a native compiler; it is not proven to have
this narrower source cause and is not closed by this repair.

Required evidence: mixed u8/u64 declaration permutations, default/C/packed
layout contracts, both actual MIR lowerers, CUDA max-end stride, and malformed
identity/arithmetic rejection. No native build or execution claim is made.

Both active `plugins/backend_cuda` and legacy `compiler/backend/cuda_backend`
consume the single checked max-end/add/align/product owner in
`compiler/backend/common/cuda_layout_extent_v1`. The backend-common module is
already a public dependency of the plugin. Each consumer supplies its actual
CUDA field sizes and existing alignment; the helper never places fields.

`cuda_type_size`, `cuda_struct_size`, and `cuda_enum_size` now return Result.
Errors propagate through array/tuple sizing, field stride/offset calculation,
aggregate construction, GEP, and instruction dispatch. Legacy construction,
GetField and SetField now use the existing destination field layout and return
errors instead of emitting guessed eight-byte slots. Both constructors validate
aggregate extent before output. Focused direct-entry load/store overflow tests
assert no memory instruction is emitted; module/GEP tests assert failure.

Authored tests (all UNRUN): real computed default/C/packed layouts and malformed
identity mapping; both actual MIR type lowerers; common arithmetic boundaries;
both CUDA constructors using small@8/wide@0; direct GetField/SetField overflow
refusal, active module/GEP failure and both consumer max-end sizing. No coverage
percentage, compiler execution, GPU execution, or runtime repair is claimed.

Packed CUDA aggregate alignment remains unqualified and is tracked separately
as `cuda_packed_aggregate_alignment_missing_2026_11_14`. The helper test with
explicit alignment1 proves only arithmetic intent, not backend packed support.
