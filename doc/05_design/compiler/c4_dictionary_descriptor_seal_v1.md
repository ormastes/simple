# C4 dictionary descriptor and artifact seal v1

Status: source implementation; execution and SOURCE availability OPEN.
This is a separate extension of the reviewed shape-1 ELF seal, not a claim that
the shape-1 implementation already certified dictionary storage.

The producer-private MIR intrinsic is
`source_region_dictionary_descriptor_v1([Const(Int(3), I64)])`. Token 3 means
ordinary resolved Struct value storage; it is not a physical representation.
LLVM resolves it to raw Struct representation 1, Cranelift to its ordinary
tagged Struct representation 2. Runtime operands, nominal scalar substitutes,
physical representations passed as compiler tokens and extra arguments reject.

The frozen physical header is `[1, 4, 64, 2, table_address, 1]`. Entry-template
rows are `[0, 8, 1, 0]` and `[8, 8, 2, actual_struct_representation]`. The 64-byte
extent describes the native dictionary CONTROL allocation. Row offsets describe
each native 32-byte ENTRY; they never authorize a header GEP or a raw field
store. The provider's dictionary operations own hashing, collision bounds,
allocation/growth, entry addressing and immediate child-owner validation.

Both backends emit actual readonly metadata and a static table relocation.
The actual object-emission owner derives shape 4 from the recognized producer
intrinsic, verifies the exact header/template/relocation, and records that shape
in the emitted seal. Shape participates in the executed-input digest. The
final ELF owner checks the expected shape and the same canonical row grammar
before issuing its bounded artifact receipt. Unknown private descriptor shapes
reject rather than disappear from partial provenance.

Struct shape 1 retains its existing grammar and formatter. Shape 4 explicitly
does not use the Struct `extent == slots * 8` rule: its extent is 64, its entry
template has two rows. A shared pure schema leaf keeps object-emission and final
ELF interpretation consistent. All previously reviewed output-FD, input-alias,
symbol-index, protection, tool/runtime admission and lifetime checks remain.

Physical representation 4 for a Struct field pointing to an actual Dictionary
is a separate op17 dependency. It remains rejected here. The compiler-only
token 3 is never serialized into physical rows. This change does not enable
runtime capabilities or certify pure/hosted/native dictionary execution.

Ten focused descriptor/schema scenarios are authored, not executed. The known
missing qualified test CLI and current resource admission blockers remain;
there is no Rust-seed fallback or repetition of old passing primitive tests.
