# ISA registry acceptance plan

Status: authored; execution, typecheck, docgen and performance UNRUN. Existing REQ-MC-009, original D0 and research §7.1–7.2 provide traceability. These are fixture contract acceptance tests, not instruction certification or complete D0 evidence.

| Selected obligation | Executable scenarios in registry_spec.spl |
|---|---|
| Preserve complete operation declaration | preserves research fields without manufacturing encoder evidence |
| Six explicit lowering states, no silent fallback | retains all six declared states; unknown lowering; implicit fallback; missing reason |
| Pinned authority and exact universe | different snapshot/ISA; equal count wrong universe; missing/extra/duplicate/unknown membership |
| Closed versioned typed envelope | schema, unknown/duplicate/missing fields, wrong type, trailing input, invalid digest/ID/revision |
| Deterministic generated coverage | reordered source, authority and evidence produce exact identical independent TSV golden |
| Verification obligations are declarations | exact two sorted typed pairs, unsupported row remains visible without invented evidence |
| Capacity refusal without truncation | exact source byte boundary, depth, row, list, text, invalid policy |
| Typed callers cannot bypass checks | mutated registry rejected by validator and both generators |

Fixtures are built in memory with explicit synthetic authority. Expected TSV and obligation pairs are independently written, not computed by production serializer. Negative helpers fail on Ok and compare actual error codes on Err. Positive helpers fail on Err. No conditional branch can silently skip missing rows/items.

After phase3_build_recovery qualifies the pure-Simple runner, request one focused run of `test/03_system/app/isa_registry/feature/registry_spec.spl`. No Rust seed fallback. Missing production imports presently make execution unavailable; no RED observation is claimed. Generate mirrored manual through existing spipe-docgen only after qualification; inspect steps and require zero stubs. Limit fix/verification to three cycles; do not rerun green checks.

Implementation must add scanner-level tests for malformed escapes/control characters and pre-allocation capacity enforcement, including instrumentation if refusal order cannot otherwise prove the bound. Runtime timings/RSS require measured fixtures after authority selection. D0 closure also requires the selected complete official extraction and real generated coverage consumer wiring; this suite alone cannot supply it.
