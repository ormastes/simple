# Differential certification admission

Authored companion to `test/01_unit/app/engine_differential_contract_spec.spl`.
These cases call the verdict rules used by the production differential harness.
They are unexecuted and do not establish that an interpreter, JIT or native
artifact ran. Actual shared programs are documented in
`doc/06_spec/02_integration/compiler/collection_req002_engine_fixtures.md`.

| Scenario | Required result |
|---|---|
| Whitespace-only stdout | Reject as no answer. |
| Failed diagnostic process with expected stdout | Reject the nonzero exit. |
| Failed certification process | Reject the nonzero exit. |
| Missing independent oracle | Reject instead of comparing agreement alone. |
| Wrong marker, extra output or internal whitespace change | Reject exact-oracle mismatch. |
| Terminal newline | Permit one LF/CRLF; reject an extra blank line. |
| Requested JIT with matching stdout | Reject absent production-owned engine witness. |
| Engine selection | Reject aliases counted twice, unknown engines or fewer than two engines. |
| Aggregate verdict | Reject any lane failure, divergence or zero-fixture run. |
| Interpreter receipt | Require exactly one execution-owner line with requested/actual interpreter and no fallback. |
| Receipt rejection | Reject missing, duplicate, wrong-mode, fallback and extra-field receipts. |
| Same-length content changes | Reject a wrong marker or altered mode field even when string length is unchanged. |

The marker file is independent expected data. Strict flags are requests, not
proof of an execution engine. Successful rule-level tests would verify verdict
logic only; REQ-002 still requires executed fixture and compiler-provenance evidence.
