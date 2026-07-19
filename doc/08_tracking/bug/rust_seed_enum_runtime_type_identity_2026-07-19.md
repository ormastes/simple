# Rust seed enum runtime type identity

Status: source-fixed; focused Rust execution pending.

The Pure implementation remains canonical. Rust LLVM and Cranelift constructors
now reuse the same stable qualified-type ID, and structural equality/hashing
include that ID. The remaining bytecode constructor path formerly rejected
`EnumUnit` and `EnumWith`; its dormant `ENUM_NEW` opcode also hardcoded enum ID
0 and truncated the hashed discriminant to 16 bits.

The bytecode compiler now lowers both constructors through the existing opcode.
`ENUM_NEW` carries the stable `u32` enum ID and full `u32` discriminant into
`rt_enum_new`, with zero or one payload field. The disassembler uses the same
wire layout.

Prevention coverage compiles and executes unit and payload constructors with
the same variant name under two qualified enum types, then checks distinct IDs
at least 2, the untruncated discriminant, NIL unit payload, and payload value.

Fresh focused Rust execution and the scheduled cross-platform seed matrix remain
pending; no seed redeploy is authorized by this source fix.

Qualified variant `PatternTest` now uses `ENUM_MATCH` with the stable `u32` enum
ID and full `u32` discriminant. Distinct assigned type IDs therefore no longer
collapse to the old hardcoded ID 0 during matching. General payload binding and
runtime-call match lowering remain unsupported in the experimental bytecode
compiler, which no production backend currently selects.
