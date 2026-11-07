# Daemon SDK publication and acknowledgement safety

Requirement: DAE-01 from the Simple Caret distributed execution plan.

The legacy serial SDK previously discarded requests after ignoring response-write
failure. Publish a matching response successfully before acknowledging its request.
On publication/identity failure, retain the request and stop polling with an explicit
publication-blocked state. On acknowledgement failure, retain failure status and
stop dispatch. The outer loop must not reset either state or invoke another handler.

Keep max_concurrent as the existing per-poll serial batch count. Preserve the old
clear_processed_requests convenience API and add a checked acknowledgement helper.
Export new status/helper names through the async compatibility facade without
claiming asynchronous execution. Validate all batch IDs before deletion; bounded
no-follow reads and basename checks constrain the legacy spool adapter.

The file spool is local compatibility transport, not authenticated remote RPC.
Private parent-directory ownership remains a service responsibility. This fix does
not create durable V1 execution receipts or guarantee crash/restart idempotency.
A restart after an uncertain effect requires domain reconciliation; remote mutation
must use the existing V2 journal path. No global runtime cleanup is introduced.

Tests inject a real response-publication failure, mismatched response identity,
acknowledgement race, successful ordering and invalid spool IDs. Authored specs and
manuals are included; admitted-toolchain execution and required core/MCP/LSP checks
remain blocked. This change must remain draft until those gates pass.

The shared native/SSpec fixture uses `assert(false)` for forbidden dispatch.
Diagnostic compilation succeeded; admitted SSpec execution remains blocked.
See the [diagnostic evidence](daemon_sdk_publication_regression_evidence_2026_11_07.md).

## Astra review: serialized envelope injection

A matching in-memory request ID was insufficient: an unescaped field continuation
could serialize request_id=other, then readers rejected the published response
after the request was acknowledged. Both writers now reject unsafe keys and every
LF continuation whose trimmed spelling begins an envelope header or field. before
creating directories or publishing. This uses the same trimming/prefix semantics
as the reader. All reserved headers are checked; it is not an ID-only special case.

Ordinary legacy multiline handling remains unchanged. No implicit escaping or
unversioned wire change is introduced, and existing multiline truncation is not
claimed repaired. Arbitrary lossless payloads require the separately versioned
transport. Other app-specific write/delete loops are not covered by DaemonRunner.
The shared native/SSpec fixture includes the injection reproducer plus adjacent
failure/boundary cases. Astra must review the final commit; runtime qualification
must still be recorded honestly before merge.
