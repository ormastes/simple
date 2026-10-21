# Deferred optional tuple payload owner evidence

Status: AUTHORED_UNEXECUTED. This manual describes executable assertions in
`test/01_unit/compiler/mono/monomorphize/deferred_tuple_payload_owner_spec.spl`.
No docgen or compiler/test runtime was admitted for this source packet.

1. Decode independently encoded Function/Struct/Class/Enum/Trait records using
   the actual DeferredMonomorphizer. Require distinct names and owners, zero
   generic parameters, nonzero starts and exact consumed offsets.
2. Load one section with all five records. Require all five names, and preserve
   refusal and diagnostics for truncated records and unknown kinds.
3. Parse a definition module and real consumer functions with the production
   frontend, lower actual HIR and MIR, and require the named consumer function
   and nonempty MIR blocks. Exercise if-val, unwrap, force unwrap, tuple alias,
   coalesce and unwrap-or without a typed definition-local workaround.
4. Require native tuple payload locals with record slot zero and i64 offset
   slot one. Distinguish bool/f64 payload slots from Optional presence. Require
   no added tuple allocation calls, one optional producer call and fallback
   calls only in the absent block.
5. Require wrong-definition and wrong-coalesce-owner rejection. Compile the
   mutable optional source/tuple alias scenario with None and Some paths.
6. Parse the original guarded Class direct `.0`/`.1` and historical two-bang
   intermediate locals for Function/Struct/Enum/Trait and the section template.
   Inspect each actual MIR GetField base shape, literal field index and result
   type against an independent expected-owner parameter. Check Bool/F64 fields
   separately from Optional's presence Bool and payload tuple envelope.
7. Require every checked absent block to terminate Unreachable without a
   GetField/GEP/load. Reassign a mutable optional to None between projections
   and require two separate checks. Require a previously recovered alias to
   retain its owner. Reject wrong nominal owner and unsupported u8 offset
   layout. Count once-only producer calls and the absence of a second wrapper
   extraction for an already recovered tuple alias.

Qualification limits: these are authored HIR/MIR and decoder oracles, all
UNRUN. Native values, offset results, branch side effects, mutable alias values,
SSA/backend layout and memory/performance targets are not proved by source
inspection. Empty tuple capability is not expanded. Original Class and
double-unwrap source oracles are authored in cycle 2; they and the complete
deferred source closure still need executable qualification before completion.
Workaround markers and the OPEN bug remain unchanged.
