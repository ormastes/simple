# Synchronous HTTP framing rejection

Source: `test/01_unit/lib/http_server/chunked_rejection_spec.spl`

Status: **code-only handoff; current docgen and runtime execution pending an
admitted Stage-4 self-hosted CLI.** This manual is synchronized to the source
on 2026-08-16 and does not claim a fresh generator receipt.

## Purpose

The synchronous HTTP server has no transfer-coding decoder. It must therefore
reject every non-empty `Transfer-Encoding` value before body dispatch instead
of treating an unsupported coding as Content-Length framing.

## Preconditions

- Use the synchronous `std.nogc_sync_mut.http_server.parser` owner.
- Do not substitute the asynchronous server, which separately supports
  bounded chunk decoding through shared `http_core` policy.
- Run with the exact admitted Stage-4 binary and retained provenance receipt.

## Operator flow

1. Submit `chunked`, mixed-case chunked, and compound `gzip, chunked` headers.
2. Submit non-chunked `gzip` and `identity` transfer codings.
3. Confirm every non-empty transfer coding returns a `501`-prefixed decision.
4. Submit a control request without `Transfer-Encoding` and confirm it passes.
5. Exercise valid, duplicate, conflicting, malformed, and oversized
   `Content-Length` values independently.

## Scenario inventory

The executable source contains 15 active scenarios and no skipped or pending
scenario:

- 6 transfer-coding/control scenarios;
- 9 Content-Length boundary and malformed-input scenarios.

## Expected evidence

- Unsupported transfer coding: decision starts with `501`.
- Absent transfer coding: empty error and body length `0`.
- Duplicate/conflicting/malformed Content-Length: decision starts with `400`.
- Body length above the configured maximum: decision starts with `413`.
- Exact maximum: accepted with the exact parsed length.

## Failure interpretation

Accepting `gzip`, `identity`, or any other non-empty transfer coding is a
fail-open framing regression and blocks AC-2. A failure confined to the async
chunk-decoding tier is a different owner and must not be hidden here.

## Security notes

This decision occurs before routing or application effects. The adjacent
duplicate Content-Length checks protect the same request-smuggling boundary;
neither guard may be weakened to make an unsupported body appear empty.

## Verification

Run once after Stage-4 admission:

```sh
"$ADMITTED_STAGE4_SIMPLE" test test/01_unit/lib/http_server/chunked_rejection_spec.spl --mode=interpreter
"$ADMITTED_STAGE4_SIMPLE" sspec-maintain scan test/01_unit/lib/http_server/chunked_rejection_spec.spl
"$ADMITTED_STAGE4_SIMPLE" spipe-docgen test/01_unit/lib/http_server/chunked_rejection_spec.spl --output doc/06_spec --no-index
```

The last command must replace this code-only synchronization with a genuine
zero-stub generated receipt before AC-10 can pass.
