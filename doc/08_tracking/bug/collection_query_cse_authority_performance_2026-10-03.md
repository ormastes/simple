# Collection query reuse requires runtime ownership evidence

The collection optimizer previously reused calls solely by method/runtime
names. MIR source calls and generated runtime calls can carry the same
`Const(Str(name))` callee. The existing ownership analysis in
`src/compiler/50.mir/mir_call_ownership.spl` documents this ambiguity.
Name matching cannot prove that a call has runtime read semantics.

The query reuse fix defaults to no runtime admission. A proof owner can supply
an explicit admitted runtime-read set; generic method names are never sufficient.
Production function and module entrypoints currently supply no such proof.
Consequently repeated runtime reads and lengths remain calls through those
entrypoints. This deliberately loses an optimization opportunity to preserve
behavior. No throughput, latency or RSS change has been measured: the admitted
self-hosted test runner is unavailable and bootstrap diagnostics are exhausted.

Follow-up acceptance:

1. Introduce an authoritative per-call origin/resolution contract shared by all
   relevant MIR producers and backend resolvers. Merely checking that a name
   is absent from one module's local definitions is insufficient.
2. Wire collection-query admission only from that contract, including source
   shadowing and external-symbol resolution negative cases.
3. Execute query legality specs and compiled shadowing/aliasing programs, then
   measure repeated-read and repeated-length workloads before and after wiring.
4. Restore performance only when semantic and backend parity gates pass.

Aggregate, string and floating constants also fail closed for query identity until
exact typed value/allocation identity can be established. Array/tuple/struct
category labels, equal string payloads and decimal float rendering are not
adequate identity proofs for the entire runtime-read family.
This issue remains open; it is not a completed full planner requirement.
