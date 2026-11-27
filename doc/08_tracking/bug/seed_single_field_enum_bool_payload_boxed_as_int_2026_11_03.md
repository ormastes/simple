# Single-field enum constructor boxes Bool payloads as integers

Status: FIXED (P1, scoped single-field enum Bool payload construction) — focused Rust MIR and direct native fixture passed; no Phase 2/3 qualification claimed.

## Static owner finding

In `src/compiler_rust/compiler/src/mir/lower/lowering_expr_call.rs`,
`MirLowerer::lower_call_expr` handles a single constructor argument in the
`arg_regs.len() == 1` branch. Its `needs_box` predicate includes
`TypeId::BOOL`, and the following fallback emits `MirInst::BoxInt`. For an
enum-with payload this encodes Bool as an integer-tagged value rather than the
runtime's tagged-boolean representation. The current multi-field enum fix does
not modify this separate single-field branch.

The static source owner review was performed against the latest release source
plus the landed multi-field patch. It found the one-field branch still includes
Bool in `needs_box` while the patched multi-field branch uses the canonical
boolean boxer. This distinct single-field path was corrected and validated
with the focused evidence below.

## Focused verification (2026-11-03)

The producer source head was `3dd808aedbc279095c470ddba618d0fa7c230645` with
tracked source diff SHA-256
`9E170C1668B9E7E0E7BCFD1C1F1A03CA08B4483946D89F79F7A2A1068ABDB9D4`.
The single-field enum MIR regression passed in the retained combined Rust unit
receipt at `C:/dev/p3new/s2_enum_bool_batch_20261103/attempt_01/result.sdn`,
SHA-256 `20918D81692ED75EEEBBCE1EDE01A6093146164CE79466B480B66192CC1F7B72`.
The dedicated native fixture `single_field_enum_bool` passed under producer
SHA-256 `36F452B0CA65D46B5FD6F5457DDADE4F158B85BB2BA5900DE20737CFAB601456`;
its executable SHA-256 is
`2709784CF27660746EC4D1254E27E6524D0F5792D980B3E89B8A8377F3E1643F`. The
aggregate result is `C:/dev/p3new/enum_array_bool_native_verify_20261103/attempt_01/result.sdn`,
SHA-256 `0B0CF11DC07B5DA8724F5000C501A83E8E5E1189A4F17BB9A643E2C66ED71B31`.
The fixture contains three conjunctive semantic checks but emits one PASS
marker; no separate assertion count is claimed.

The independent mechanism review passed against
`C:/dev/p3new/enum_array_bool_native_verify_20261103/attempt_01/mechanism_receipt.sdn`,
SHA-256 `790484CE7BF7206B9911448A476DECE01C20BF47781EF6FB1E8581A4F3D35A4C`.
It verified the narrow enum Bool conversion through `rt_value_bool` to
`rt_enum_new` rather than integer boxing.

This is bounded direct-native evidence for the named fixture only. The
campaign explicitly records `phase2_qualification: false` and
`phase3_qualification: false`. No broader enum behavior or tuple getter
behavior is inferred.
