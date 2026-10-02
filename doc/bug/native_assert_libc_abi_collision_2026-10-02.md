# Native assertion collides with libc __assert

The Linux class metadata fixture exposed a distinct native assertion crash:
the pure-Simple parser emits `__assert(condition[, message])`, HIR accepts
the builtin, but MIR previously emitted it as an ordinary external call.
On Linux it resolved libc's incompatible assertion entrypoint. Windows can
instead fail to link; neither host may treat this as a C ABI call.

## Contract and fix

- REQ-NATIVE-ASSERT-ABI-001: a true assertion continues and a false assertion
  terminates through the existing runtime panic plus nonreturning MIR abort.
- REQ-NATIVE-ASSERT-ABI-002: optional diagnostic expressions remain evaluated
  in ordinary argument order exactly once, matching the interpreter's call
  evaluation. Supplied diagnostics are preserved; the default is `assertion failed`.
- REQ-NATIVE-ASSERT-ABI-003: no `__assert` native external reference is emitted.

The MIR direct builtin dispatch now owns this lowering. It uses the existing
condition lowering and text conversion, with no new host API or runtime ABI.
This fix is independent of HirExpr presence, class metadata and static storage
fixes. Its code can be shared by Linux and Windows next-generation producers.

## Acceptance and current evidence

`native_assert_builtin_lowering_spec.spl` inspects production lowering.
Native fixtures in `test/fixtures/codegen/assert_builtin_native_*` require:

| Fixture | Required execution result |
| --- | --- |
| success | exit 0; condition-once, message-once, assert-native-ok each once |
| failure | nonzero; supplied marker; no UNREACHABLE marker; no SIGSEGV |
| default_failure | nonzero; assertion failed; no UNREACHABLE; no SIGSEGV |

Run with both actual self-hosted Windows and Linux compilers, no unresolved
stub fallback, frozen source and private producer-bound caches. A seed-only
fixture compile does not exercise the changed MIR implementation.
Source fix and tests are implemented. Native candidate and SSpec execution
are pending admitted build capacity; no runtime PASS is claimed.
