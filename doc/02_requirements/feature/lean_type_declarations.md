# Selected requirements: bounded C2 declaration step

Authority: the existing robust revised plan, lane 07 C2 / REQ-MC-007, and root's instruction to implement representation-preserving declarations through both retained backend owners. This is an implementation refinement of selected contracts, not a newly selected replacement scope.

| ID | Required behavior | Executable oracle |
|---|---|---|
| C2-D1 | Export actual registered acyclic structures and enums, including payloads, via full and regeneration APIs | plugin declaration cases; compiler-owner integration cases |
| C2-D2 | Resolve exact qualified nominal symbols and kinds; deterministically emit dependencies first | map-order, same-short-name, dependency and mismatch cases |
| C2-D3 | Preserve primitive width mapping and source identity, field order/offsets, enum tags, C export identity | exact declarations and typed metadata cases |
| C2-D4 | Reject incomplete/unsupported declarations before mutating the declaration builder | missing symbols, cycles, unions, bitfields, malformed names, duplicates, invalid layout and builder retention cases |
| C2-D5 | Thread nominal context through real module function signature export | identityPacket actual MIR function case |
| C2-D6 | Emit no declaration proof placeholders or invented proof closure | actual compiler-owner output lacks axiom/sorry; module closure remains open |

Supported: ASCII-qualified acyclic structs/enums, empty semantic declarations, existing exact primitives, and supported array/slice/tuple/result nesting. The complete C2 remains ACTIVE: recursive/mutually recursive forms, unions, bitfield refinement, additional type families and full aggregate operation semantics are not completed here. Unsupported forms return CompileError rather than placeholder types.
