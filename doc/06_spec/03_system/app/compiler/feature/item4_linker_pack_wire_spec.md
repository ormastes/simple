# Linker pack transport

Requirement: ITEM4-REQ-010. **UNRUN — authored manual, not canonical docgen.**
Executable: `test/03_system/app/compiler/feature/item4_linker_pack_wire_spec.spl`.

1. Encode a complete request and policy, preserving maximum unsigned words and
   literal paths; decode and compare scalar values and paths.
2. Reject overflowing, negative, malformed, noncanonical and narrowing integers,
   unknown modes, inconsistent argument counts and NUL paths.
3. Round-trip an unsuccessful receipt without inventing successful accounting;
   reject malformed/trailing response fields.
4. Bind every policy scalar to a domain-separated SHA-256 identity. Compare the
   full digest with an independently computed .NET oracle, then change workers
   and prove the identity changes.
5. Invoke the real provider-side native adapter with an unsupported target and
   preserve its typed rejection and policy identity through both arenas.
6. Reject wrong commands/operations and undersized response reservations before
   adapter dispatch.
7. Admit the supported provider query and reject incompatible host ABI and
   unsupported query-target payload at the provider boundary itself.

These are wire and adapter scenarios. They do not establish mapped-provider
execution, output loader behavior, memory enforcement, coverage or release PASS.
