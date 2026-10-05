# Named enum field projection drops its declared owner

Parent bug: phase2_subsystem_helper_mir_failures_2026-10-05.
Status: focused compiler fix authored; unit/native execution UNRUN.

All six preserved Phase2 main-verdict helper attempts failed. Two common
diagnostics name ProcessObservationPacketKindV4 as an unsupported Struct
operator receiver. Their exact process_ops source expressions, lines 1094 and
1117 in frozen916, are `frozen_receipt.packet.packet_kind != ...Frozen` and
`cleanup_receipt.packet.packet_kind != ...CleanupFrozen`, both typed parameter
projections. This is not evidence that the original declaration was a struct.

`remember_field_projection_provenance` retains the nested type's name in
`struct_value_syms`, but its declared-type dispatch only handles Dict, Array
and Slice. It drops Named HIR metadata. Meanwhile `local_enum_type_id` requires
that Named metadata and registered enum identity before admitting enum
equality. Without it the field's Struct-shaped MIR representation takes
ordinary struct operator dispatch, producing the reported diagnostic.

The fix carries the existing declared Named HIR type onto the projected local.
It does not infer enum identity from a name, invent a discriminant, cast enum
values to integers, or change process authority comparisons. Ordinary Named
aggregate fields retain their own declared identity as well. Missing metadata
and invalid field indexes remain unknown. Arrays keep their separate runtime
array marking.
Enum equality admission also checks the qualified declaration map when the
symbol has an owner, so a projected ordinary struct cannot borrow enum storage
from another module's same-named enum. Ownerless legacy enum lookup is unchanged.

Regression coverage:
- `named_field_projection_provenance_spec.spl`: distinct owner IDs, absent and
  out-of-range metadata, array/scalar neighbors and an unrelated same-name
  struct/enum declaration collision (four cases).
- `native_named_enum_parameter_projection.spl`: frozen equality, different
  variants/acknowledged rejection, inequality and nested array neighbor (six
  checks), both native backends with a producer containing this fix.
- The original/typed shared-I/O pair isolates whether the current producer
  supports a source workaround. It does not prove a rebuilt compiler fix.

Memory/performance: adds one existing local-HIR metadata insertion per Named
field projection, bounded by lowered function locals and existing owner scope;
no runtime object representation, new global cache or process lifetime changes.
Compile elapsed time and peak RSS comparisons remain UNRUN until the corrected
producer and paired current-producer probe receipts exist. Preserve all valid
caches and failed attempts. No running Phase2/3/4 input changes from this lane.

This patch addresses the proven projection omission only. Result factory
inference, optional text, enum-arm and I64 iterable failures remain distinct
until their own probes or source traces establish a shared cause.
