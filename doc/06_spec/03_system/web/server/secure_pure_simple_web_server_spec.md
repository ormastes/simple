# Secure Pure-Simple production web server

Source: `test/03_system/web/server/secure_pure_simple_web_server_spec.spl`

## Purpose and audience

This manual is for operators and reviewers validating REQ-002 response framing
through the canonical synchronous Pure-Simple web server. It covers positive,
edge, and error behavior at the serializer and over a real loopback TCP
connection. It does not claim production TLS completion.

## Preconditions

- Use the exact current-source Stage-4 full CLI whose adjacent provenance file
  passes the repository admission contract.
- Never substitute the Rust seed or a Stage-2/3 bootstrap compiler.
- Run from the repository root with loopback bind/connect available.
- Treat a missing admitted CLI as `TEST_BLOCKED`, never PASS or skip.

## Primary operator workflow

1. **Construct one valid application response.** Add one safe trace header.
2. **Serialize through the server-owned framing writer.** Require one canonical
   length, forced close, no transfer coding, the trace header, and the complete
   body.
3. **Construct conflicting application response framing.** Supply mixed-case
   and whitespace-bypass framing fields, an invalid token name, control-bearing
   values, and an unsafe attempted security-header override.
4. **Reject overrides, injection, and incomplete framing.** Prove every hostile
   value is absent and the canonical header block remains singular.
5. **Bind the production listener.** Use an ephemeral loopback listener and a
   real client/server stream pair.
6. **Route one request to the hostile application handler.** Traverse request
   parsing, routing, default security headers, bounded `write_all`, and close.
7. **Verify the complete server-owned wire response.** Read through EOF and
   require the exact body plus the safe frame-denial default.

## Scenario narratives and absolute oracles

- **Positive:** a safe application header survives beside exactly one
  `Content-Length: 2`, one `Connection: close`, no `Transfer-Encoding`, and
  body `ok`.
- **Edge:** case variants, leading/trailing whitespace, colon-bearing names,
  tabs, CR/LF injection, and conflicting framing values are all absent.
- **Error/live:** a hostile routed handler cannot suppress the safe
  `X-Frame-Options: DENY` default or change the complete loopback wire body.
- Existing request-framing scenarios also reject traversal, duplicate lengths,
  unsupported coding, singleton-security conflicts, and malformed request
  lines before dispatch.

## REQ traceability

| Requirement | Executable source | Positive | Edge | Error/live |
|---|---|---|---|---|
| REQ-002 / AC-2 | `test/03_system/web/server/secure_pure_simple_web_server_spec.spl` | valid application header | conflicting/control-bearing fields | real loopback hostile handler |

## Quality scorecard

Status: **TEST_BLOCKED**. Static quality and repository guards are recorded in
the lane state. Runtime execution, `sspec-maintain scan`, and `spipe-docgen`
were not run because no provenance-admitted Stage-4 CLI is available. This
Markdown file is a synchronized manual, not a generated zero-stub receipt.

## Findings and remediation

The repaired writer is the sole response-framing owner. If a future run emits
an application framing field, duplicate canonical field, injected line, missing
security default, partial body, nonzero test exit, or missing scenario count,
the lane fails. Repair the owning writer or spec; do not weaken the oracle.

## Evidence and provenance

Retain the admitted CLI absolute path, SHA-256, adjacent provenance path,
source revision, exact test command, exit status, scenario totals, maintenance
scorecard, and docgen `0 stubs` receipt. The canonical command order is in
`doc/03_plan/sys_test/secure_pure_simple_servers.md`.

## Compatibility and limitations

GAP-TLS-3 still blocks encrypted application traffic. Loopback plaintext in
this spec proves the canonical parser/router/writer socket path only; it is not
production HTTPS evidence. No executable `.spl` belongs under `doc/06_spec`.
