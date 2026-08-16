# Parallel Ownership and Storage Layout NFRs

Status: selected from the user-provided 2026-08-12 architecture brief.

- NFR-PAR-001 Determinism: critical commits use an explicit canonical order or fixed reduction tree and emit a receipt hash.
- NFR-PAR-002 Memory boundedness: default task/result mailboxes have a finite item or byte bound and backpressure behavior.
- NFR-PAR-003 Safety: unproven dynamic-index disjointness, raw process pointers, and unknown dynamic transport fail closed in safe/critical paths.
- NFR-PAR-004 Compatibility: public ABI, wire, persistent, and MMIO layouts remain byte-compatible unless an explicit conversion is requested.
- NFR-PAR-005 Performance evidence: layout, queue, allocator, SIMD/GPU, false-sharing, and NUMA choices expose measurable receipt/counter hooks; no kernel-only speed claim is sufficient.
- NFR-PAR-006 Portability: host thread, host process, interpreter, native, and supported device paths share one contract or report an explicit unsupported receipt.
- NFR-PAR-007 Assurance: no child or environment input can lower a project assurance pin; critical denies implicit downward mutable transfer and unbounded safe mailboxes.

| NFR | Verification mechanism |
|---|---|
| NFR-PAR-001 | randomized completion replay with stable receipt/hash |
| NFR-PAR-002 | bounded queue occupancy/backpressure/cancellation tests |
| NFR-PAR-003 | compile-fail and malformed-envelope tests |
| NFR-PAR-004 | ABI/layout property tests |
| NFR-PAR-005 | reproducible benchmark/receipt harness |
| NFR-PAR-006 | parity matrix with blocked rows retained |
| NFR-PAR-007 | policy resolution and critical diagnostic tests |

The focused executable
`test/03_system/feature/language/parent_commit_piped_result_spec.spl` traces
NFR-PAR-001, NFR-PAR-002, NFR-PAR-003, and NFR-PAR-006 through deterministic
typed receipts, finite ingress/reader budgets, malformed/replay fail-closed
behavior, and an explicit blocked native-tooling row. Its authored mirror is
`doc/06_spec/03_system/feature/language/parent_commit_piped_result_spec.md`.
These references become execution evidence only after an admitted pure-Simple
native verdict and do not substitute for the full portability matrix.

`test/03_system/feature/language/actor_channel_authority_spec.spl` adds partial
NFR-PAR-002/NFR-PAR-003 coverage through one-slot mailbox/reply budgets, retained
high-water evidence, returned credit after consumption, and fail-closed unknown,
full, and stopped operations. Its authored mirror is
`doc/06_spec/03_system/feature/language/actor_channel_authority_spec.md`; it is
not NFR-PAR-006 parity evidence and remains native/docgen blocked.
