# Native single-scalar validation rejects ASCII in the character wire probe

Canonical ID: `native_text_scalar_validation_failure_2026_10_18`.
Status: OPEN; authoritative bug DB reconciliation pending a qualified full CLI.

The genuine public native build of source `b4ac2495d01a25dbc564c6dff12621fe61c87897`
using compiler `b441c88d477950d2118edf04ddaae1eefb9b5e91942dc821836d108ba776f1ab`
compiled and linked successfully. Its executable returned 13: the expression
`text_is_valid_utf8("a") and text_codepoint_len("a") == 1` evaluated false.
The earlier empty/two-character rejection controls did not fail. Character
conversion checks occur later and were NOT reached. This does not isolate
which validation helper failed or establish an ABI root cause.

The executable SHA-256 is
`dc964eba555dd441a3141e07d4e838b4c876b11bafe8c72c6c3bd9e3cc2a8251`.
Evidence remains at `C:/dev/p4char`: `result.env`, `guard.env`, compiler logs,
retained objects and capsule receipts. The guard completed with exit 13,
quiescent process tree and peak RSS 2,283,604 KiB. Compilation also emitted
an invalid-array-handle diagnostic; the generated program's stderr was empty.
No successful character conversion or complete codec repair is claimed.

The provisional probe workaround reuses the existing pure `utf8_decode_one`
and `utf8_encode_one` owners. It accepts exactly one decoded scalar only when
re-encoding reproduces every original byte. This distinguishes malformed
sequences replaced by the decoder from a genuinely encoded U+FFFD. It does
not change the production SIMD validation API. Workaround native verification
is pending; its commit and actual result must be recorded before closure.

Intended recovery: investigate the real text/SIMD facade and native calling
convention, then require ASCII, BMP, astral, empty, multiple-scalar and invalid
UTF-8 controls through the public helpers. Restore the original probe helper
from the recovery commit only after that regression passes. Compiler/runtime
UTF-8 ownership lane is the background fix owner, currently unassigned.

## 2026-10-18: second focused native attempt

Workaround commit `6e8d05eee4817157e34b64ce6a091f3a4bf665c4` passed the
genuine native probe with the same immutable compiler. Evidence at
`C:/dev/p4char2/result.env` records compile exit 0 and run exit 0; stdout is
`CHAR_WIRE_ASCII_VALID=true` followed by `CHAR_WIRE_SCALAR_CAST_PASS`.
Executable SHA-256:
`89c5d579e40e5b43b40dac6fbd9597a911a3301fd1e51017e9813fa7121c0973`.
The guard records peak RSS 2,540,840 KiB and a complete, quiescent process tree.
This qualifies the pure validator plus typed scalar conversion and enum
extraction for the fixture cases. It does not resolve the original public
validation API failure, or qualify the production CharLit codec.
