# Collection binding HIR ownership

Authored manual, 2026-10-03. Source: `test/01_unit/compiler/driver/collection_binding_owner_spec.spl`. This document is not generated runner output. The three scenarios have not been executed in this session.

Partial traceability: REQ-003 (resolved binding identity) and REQ-007 (typed HIR admission). The fixture constructs a local method declaration, symbol table, receiver type, source ownership, and canonical ABI fingerprint. Each case calls the production `collection_driver_validate_binding_v1` function.

| Scenario | Setup and action | Observable assertion |
|---|---|---|
| Matching owner and reused local ID | Bind method ID 42 in `first.spl`; validate against that module and a second module also containing ID 42. | The actual owner is accepted; the unrelated module is rejected despite the identical numeric ID. |
| Stale declaration evidence | Independently change the signature fingerprint, receiver classification, compilation backend to `auto`, or symbol ID to an absent declaration. | Every mismatch returns an error. Each check starts from an otherwise valid binding. |
| Foreign or stale source ownership | Change the symbol's defining module, then independently change the function's source file. | Both ownership mismatches return errors despite matching local IDs. |

The positive case supplies the exact module path and explicit `native` backend. A canonical declaration digest checks typed signature identity; it intentionally does not authenticate implementation behavior. Fixture receipt strings are test inputs, not certificates of purity, cost, or backend correctness.

These tests cover the ownership validator directly. They do not demonstrate automatic builtin binding discovery, complete configured compilation, rewrite safety, or cross-engine execution. The driver session manual covers the separate shared admission lifecycle.
