# Shared parse cache: Windows/Linux acceptance

Scope: the user's requested positive/negative system tests, verification on both
hosts, and deployment after both hosts pass. This records that selected scope;
it does not propose a broader cache-sharing feature.

Status: **BLOCKED / NOT DEPLOYED**. Candidate base: `0d722af3d62e3b693af8bef475cf227d7f55d69e`.

| ID | Required behavior | Required evidence |
|---|---|---|
| REQ-001 | Share immutable flat pools only for equal raw source, parser input, parser/codec identity, cfg decisions, feature identity, and portable logical path. | Production key/preprocessor tests; actual equal-key cell on both hosts. |
| REQ-002 | A shared hit rebuilds the real AST, retaining its function body and excluding prior mutable parser state. Malformed pools recover by parsing. | Native probe checks literal 73 and parser-call delta, plus SSpec malformed-pool recovery. |
| REQ-003 | Reject corruption, truncation, wrong address, wrong envelope and wrong codec; preserve the original winner. | Production decode tests and isolated real-cell negative runs on both hosts. |
| REQ-004 | Reject traversal, ambiguous logical paths, linked/reparse source/cache paths and host-private payload paths. | Production logical-path tests, existing root-admission test, and native no-follow negative runs. |
| REQ-005 | Require sealed source/parser authority and retained producer lineage. A different producer executable is not automatically incompatible when the portable parser contract agrees. | Missing/wrong/mutated authority runs; hash-bound source, binary, runtime, cell and host receipts. |
| REQ-006 | Publish atomically without replacement; identical simultaneous writers converge; conflicting bytes cannot replace a winner; interrupted temporary writes cannot become hits. | Two actual concurrent native workers, reader during publication, interrupted writer and restart receipts. Sequential calls do not prove concurrency. |
| REQ-007 | Keep private frontend/HIR state, native objects/executables, runtime handles, processes, session guards and local paths outside cross-OS sharing. | Distinct host/producer/backend cache roots and scope witnesses; production rejection of foreign private entries; inspect actual artifacts and target formats. |
| REQ-008 | Deploy only after both native directions and all negative/isolation cases pass through the SOSIX capacity owner. | Complete matrix, independent review, immutable candidate/config, deployment receipt and one post-deployment bounded smoke per host. |

## Ownership and compatibility

The shared boundary carries **frozen encoded payloads**, never pointers, loans,
OS handles or mutable parser owners. Each worker owns its private frontend, HIR,
native outputs and process state. The manager owns root admission and capacity;
workers publish new cells with no-replace semantics and validate the winner.

`target_identity` hashes actual selected bytes and cfg decisions, not the target
triple spelling. Target-neutral modules can therefore cross Windows/Linux when
the complete key agrees. A parser source or codec change changes admission;
the native producer binary hash is retained as provenance rather than blindly
added to the portable key. Native object/executable identity remains private.

`SHARED_PARSE_CAS HIT` is emitted before hydration. It alone never satisfies
REQ-002. Existing unit tests using `validated-pool-a` and two OS-shaped path
strings establish neither a valid AST nor two operating systems.
