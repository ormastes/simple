# Lean nominal value semantics

The existing C2 declaration owner emits Lean structures and inductive types. A structure constructor is its qualified `.mk`; each declared field generates a qualified projection. An inductive variant generates its qualified constructor; its MIR discriminant is metadata, not a Lean constructor ordinal. The new body translator uses those declaration names directly and checks exact MIR types before emitting Lean applications.

Primary references already retained in this session: official Lean 4.30.0 source and the reviewed C2 declaration packet (`lean-type-declarations-20261018/revision2`). No new external behavior or new primitive representation is assumed. Existing fixed-width integer constants retain BitVec.ofInt semantics. Matching Lean types alone cannot distinguish signed and unsigned MIR fields, so equality uses the existing exact MIR type serialization after both types pass the context mapper.

This is source-level translation work. Generated terms have not been elaborated in Lean, and no production/native refinement theorem is claimed.
