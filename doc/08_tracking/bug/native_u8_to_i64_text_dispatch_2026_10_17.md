# Native numeric u8.to_i64 resolves to text parsing

Date: 2026-10-17
Bug: BUG-NATIVE-U8-TO-I64-TEXT-DISPATCH-20261017
Database registration: pending; no admitted database tool available.
Status: OPEN producer dispatch defect; bounded fixture workaround unqualified.
Recovery: ca73ab76f75ec720323869606777ee31bbfc0c7f.

NativeChar feature cycle2 built79 genuine selected SPL COFF objects, strict-linked without FORCE/IGNORE and executed its exact reviewed candidate ONCE. SHA2561E0275F949CAB5C91A13B81251072496C9F89E1F18EF79A78D595AA0B13A8C9F exited1 with exact `FAIL unicode-scalar-char: rendered byte contents 65`, stderr0,0.0236436seconds, unchanged pre/post hash. Actual receipt, exclusive ledger and raw outputs remain in external unicode-scalar-native-char-cycle2/strict-link.

The first ASCII control passed numeric character cast-back, actual HirExprKind.CharLit payload cast-back and rendered byte length1 before failing the byte contents comparison. Later Unicode/invalid controls did not execute; no full primitive qualification is claimed.

Retained fixture COFF gives a concrete cause distinct from a claimed character-encoding failure. In actual unicode_scalar_char_case_v1, offset0x26d loads the typed character scalar and0x273 calls rt_char_from_code. Offset0x2d7 calls rt_string_bytes. Offset0x36b calls rt_bytes_u8_at for the indexed byte, then the source .to_i64 call is emitted through text pointer/interpolation conversion, rt_string_len at0x382, rt_string_new at0x38d and rt_string_to_int_lenient at0x395. The expected integer array uses the separate rt_array_get and rt_value_as_int_wide path. No actual byte values are invented from this static evidence.

The frozen runtime source confirms rt_string_bytes produces correctly tagged byte array values and rt_bytes_u8_at returns a raw0..255 integer. Treating that numeric receiver as text is the demonstrated wrong dispatch. Actual source method_calls_literals.spl contains both text-to_i64 and numeric-conversion paths; fixing that production dispatch owner requires its own reviewed compiler qualification and is not implemented here.

The temporary fixture workaround replaces ONLY bytes[index].to_i64() with (bytes[index] as i64). This is an ordinary numeric widening of an actual u8, not a text-pointer cast. It keeps the exact expected-byte comparison, loop bounds, ASCII/Unicode/NUL/U+0003/escape/boundary/invalid controls and actual character/enum/rendering checks. No production helper, runtime ABI, generated codec, receiver admission or denial policy changes. The immediate workaround tag records this bug and full intended-code recovery hash.

External cycle3/source-freeze preserves the original fixture, raw COFF excerpt and inverse proof: undoing this one expression and tag restores the complete previous fixture byte-for-byte, with no other check edits. The actual full disassembly and input object hashes remain in cycle2/strict-link. Applied workaround SHA is recorded in final freeze metadata; recovery does not authorize reset or deletion of prior evidence.

Next attempt, only after root source/command/resource approval, is FINAL NativeChar feature cycle3/3 using the SAME cycle1 persistent cache with ordinary invalidation, exact0CD6 producer and own D9 runtime/header lineage. No automatic fourth attempt or feature-budget relabel. Cycle1 compile failure and cycle2 actual runtime failure remain immutable. BDD, doctest, complete Unicode primitive qualification, generated-codec/reader consumer and broader compiler/lib/MCP/LSP/admission gates remain UNRUN.