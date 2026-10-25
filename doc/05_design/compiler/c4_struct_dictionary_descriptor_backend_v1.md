# Typed Struct to Dictionary descriptor extension

Status: source implementation; op17 runtime/coherent acceptance OPEN.
This extends the frozen architecture contract `c4_struct_dictionary_edge_v1.md`;
it does not enable SOURCE admission or turn physical metadata into nominal proof.

Private token 5 means ordinary Dictionary storage. It is accepted only by
`source_region_struct_descriptor_typed_v1([containingStructSymbol, kind, codec,
...])`. All operands are compiler I64 constants. The actual module type owner
must resolve the containing Struct, field count, uniform word offsets and every
declared field type. Token 5 requires kind 2 and an exact Dict(I64, Struct(value
SymbolId)) field with a resolved value layout. Token 3 retains its ordinary
Struct meaning. The old pair-only route rejects both token 5 and raw repr4.

LLVM and Cranelift consume their actual module type definitions, never a caller
name or guessed runtime nominal ID. A semantic recipe digest binds the owner,
field index, declared nominal type and resolved direct value-layout facts.
The actual emitted-object record carries this digest alongside physical bytes;
the executed-input digest and final retained receipt bind the same record.
Incoming born-dictionary recipe matching remains the typed planner/site/body
owner's obligation before lowering to the private operation.

Both backends resolve a validated Dictionary field to physical shape-1 row
`[offset, 8, 2, 4]`. Representation 4 denotes the actual tagged Dictionary
family; it is not a literal tag-bit value. It is refused for scalar, immutable
and shape-4 Dictionary VALUE rows. Compiler tokens never enter physical rows.
No descriptor offset authorizes direct header field stores: op17 owns dictionary
registry/current-backing validation, native-owner-before-region locking,
same-control/generation checks and indivisible store/epoch advancement. Existing
operations 7/8/9 continue to reject dictionary-field writes.

The backend change adds compiler-only recipe transport, not fields to ordinary
runtime objects or a new global registry/lock. Actual op17/native/pure/hosted
availability and the born Root→Dictionary→Child retained-alias Stale scenario
remain unexecuted prerequisites. Eight nominal/schema helper scenarios are
authored but UNRUN; no old passing primitive test is repeated.
