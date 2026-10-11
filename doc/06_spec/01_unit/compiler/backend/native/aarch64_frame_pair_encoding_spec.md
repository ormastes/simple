# AArch64 frame pair encoding

Requirement: REQ-AARCH64-FRAME-PAIR-001.
Executable source: test/01_unit/compiler/backend/native/aarch64_frame_pair_encoding_spec.spl.
Four scenarios with real exact-byte assertions and zero placeholders.

| Scenario | Instruction | Expected little-endian bytes |
|---|---|---|
| Selector frame save | STP x29,x30,[sp,#-16]! | fd 7b bf a9 |
| Selector frame restore | LDP x29,x30,[sp],#16 | fd 7b c1 a8 |
| Offset store control | STP x29,x30,[sp] | fd 7b 00 a9 |
| Offset load control | LDP x29,x30,[sp] | fd 7b 40 a9 |

The two frame scenarios use the selector's four-operand Reg/Imm instruction
shape; the controls use the ordinary three-operand Mem shape. Each calls
encode_inst_aarch64 with a fresh encode context and compares all four bytes.

Reproduce with an admitted self-hosted runtime:

```text
<runtime> test test/01_unit/compiler/backend/native/aarch64_frame_pair_encoding_spec.spl --mode=interpreter
```

Provisional current-owner source-inline evidence improved 2/4 to 4/4. Required
admitted runtime and native qualification remain outstanding; the retained
global-address integration spec is not claimed to pass. Evidence and limits:
doc/08_tracking/bug/aarch64_frame_pair_operands_2026-10-11.md.
