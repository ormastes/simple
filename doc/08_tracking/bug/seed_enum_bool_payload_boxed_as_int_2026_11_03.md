# Multi-field enum constructor boxes Bool payloads as integers

Status: FIXED (P1, narrow multi-field enum Bool payload construction). No Phase 2 or Phase 3 qualification is claimed.

## Scope and repair

The original failure was the `true optional bool projection` assertion in the
generic 24-check native tuple fixture. The multi-field enum constructor path in
`src/compiler_rust/compiler/src/mir/lower/lowering_expr_call.rs` included Bool
in its integer `needs_box` arm and emitted `BoxInt`. The correction excludes
Bool from that integer arm and uses `box_scalar_for_tagged_slot(ANY, BOOL, arg)`
for the multi-field payload, preserving the runtime's tagged-boolean
representation. This record is intentionally limited to the multi-field enum
constructor path; the single-field constructor and typed-array method paths
remain separate OPEN P1 findings below.

The source patch SHA256 is
`EC2ED6A77AE3A2CD715B3FCB2B2C0A1C511D2B1F852DF3767588DCBEC714330B`, applied
to source head `7137e3c2c05cab49562d277372ad1050d1b8d835`.

## Focused evidence

The immutable uncertified seed built from that patch is
`DDA32D9110D28691928F1A3D03D59C50307D08B0FD357903CEB3F4B955392B68`; its
build result at
`C:/dev/p3new/s2_enum_bool_seed_20261103/build_attempt_01/result.sdn`
(SHA256 `F524D927247EA7A441094584A76AD709E73CAA9D0075B001B66C72ACFE2D2874`)
records rc 0, 250.0 seconds, and 3.61 GiB peak tree RSS.

The MIR unit `sanitized_multifield_enum_constructor_boxes_bool_payload_as_bool`
passed once (result
`C:/dev/p3new/s2_enum_bool_seed_20261103/attempt_01/result.sdn`, SHA256
`B239B42AA03A16E329D12D9F60419CCB01FD946D8CFDD963244DC13E2D67F1D5`). It
covers false, true, and numeric payload ordering.

The bounded PowerShell native campaign at
`C:/dev/p3new/tuple_abi_generic_bool_verify_20261103/attempt_01/result.sdn`
(SHA256 `295E3F382CC10A75B487D61A4F2A912B03F4E47963040FF0BA8C3935D5595A50`)
reports `NATIVE_PASS` for the generic 24-check case. Its case result SHA256 is
`1125042CE294E2BB7F4ACE8498ACE6732B0764DBDC3A140036A7B4FE0E35C28A`; the
executed executable SHA256 is
`6E5AE59287B7B0572C4F701CE34312A8C2C998C21CDF1EF2125EB3612FE9B65E`. The
later offline mechanism receipt
`C:/dev/p3new/tuple_abi_generic_bool_verify_20261103/attempt_01/mechanism_receipt.sdn`,
SHA256
`55CF450498E0E77F915AA65F4848D1842D774885D46A31A0EB0CE4DDE439D322`,
received Astra exact-receipt PASS. The receipt supports this narrow
multi-field construction fix; it does not qualify Phase 2/3 or close the
separate findings below.

The previous failing result on the D18 seed is retained as pre-fix history; it
is superseded only for this multi-field constructor case. This does not assert
a tuple-getter ABI defect, and does not imply that every enum Bool construction
or collection operation is correct.

## Related independently scoped fixes

- Single-field enum Bool payload construction is FIXED in its scoped path:
  `doc/08_tracking/bug/seed_single_field_enum_bool_payload_boxed_as_int_2026_11_03.md`.
- Typed array `.push` / `.index_of` Bool boxing is FIXED in its scoped paths:
  `doc/08_tracking/bug/seed_array_method_bool_value_boxed_as_int_2026_11_03.md`.

These scoped fixes do not imply that all BOOL boxing sites are correct.
