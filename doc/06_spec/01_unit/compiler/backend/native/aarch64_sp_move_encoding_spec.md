# AArch64 stack pointer move encoding

Requirement: REQ-AARCH64-SP-MOVE-001.
Executable source: test/01_unit/compiler/backend/native/aarch64_sp_move_encoding_spec.spl.
Four scenarios, zero placeholders.

| Scenario | Instruction | Expected little-endian bytes |
|---|---|---|
| Frame pointer setup | MOV x29,sp | fd 03 00 91 |
| Stack pointer restore | MOV sp,x29 | bf 03 00 91 |
| Explicit SP self move | MOV sp,sp | ff 03 00 91 |
| General register control | MOV x1,x0 | e1 03 00 aa |

Each scenario constructs the actual A64_OP_MOV machine instruction and calls
encode_inst_aarch64 with a fresh encode context. It asserts equality against
the full four-byte result. The first three require ADD-immediate #0, whose
register 31 denotes SP; the control requires ORR shifted-register.

Reproduce with the admitted self-hosted runtime:

```text
<runtime> test test/01_unit/compiler/backend/native/aarch64_sp_move_encoding_spec.spl --mode=interpreter
```

Recorded bootstrap diagnostic: current release source-inline baseline 1/4,
repaired 4/4. This is provisional evidence; admitted runtime qualification and
the compiler/core/MCP/LSP gates remain outstanding. Evidence and limitations:
doc/08_tracking/bug/aarch64_sp_move_encoding_2026-10-11.md.
