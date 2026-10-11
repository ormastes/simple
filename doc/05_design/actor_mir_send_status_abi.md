# Actor send status bridge repair

REQ-ACTOR-STATUS: the i64-returning MIR actor send bridge calls the registered
i64-returning rt_actor_try_send function. Replace its extern declaration and
single call; preserve parameters, return type, unsafe capability and dispatch.

Update the existing actor_runtime_abi_contract_spec.spl to import std.spec,
inspect the canonical runtime owner, distinguish void send from try-send status,
and check that all four retired generic hooks refuse the unsafe legacy ABI.
Retain the LLVM spawn negative assertion, even though it currently fails.

Cached bootstrap source-contract evidence is diagnostic only. Cycle 1 exposed
the removed owner path; cycle 2 executed one case and failed on the retained
LLVM spawn assertion. Do not replay unchanged failing or passing checks.

Before admission, verify the pure compiler/lib and MCP/LSP checks, interpreter
integration smoke, native runtime smoke, and real accepted/rejected actor-send
status behavior with an admitted self-hosted producer. No such producer was
available for this repair. No bootstrap rebuild or cache deletion was performed.

Agent ownership: root implements the narrow bridge repair; backend_audit reviews
the exact boundary and source contract independently. No broad generated work.
