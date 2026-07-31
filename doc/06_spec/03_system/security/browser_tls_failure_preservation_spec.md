# Browser TLS failure classification and preservation

> The runtime and hosted broker expose only stable TLS/network failure codes.
> Certificate failures never commit, retry, redirect, learn HSTS, or replace
> the previously committed document, CSP, title, or history.

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 2 | 2 | 0 | 0 |

## At a Glance

| Field | Value |
|---|---|
| Status | Implemented static; execution held |
| Source | `test/03_system/security/browser_tls_failure_preservation_spec.spl` |
| Requirements | REQ-WEB-BROWSER-009, 011, 014, 020, 021 |
| Updated | 2026-07-31 |

## Scenarios

### should expose stable failures while preserving committed browser state

1. **Commit one HTTPS page and capture its security state**
   - Load one bounded HSTS entry.
   - Commit a titled page with CSP, DOM content, history, and a script fetch.

2. **Reject with broker-owned stable failures**
   - Exercise hostname, certificate, protocol, timeout, and network codes.
   - Require JavaScript to receive the exact stable code and fixed message.
   - Collapse raw platform text and TLS labels on HTTP to the generic network
     failure.

3. **Fail a replacement HTTPS navigation without retrying**
   - Return status zero with empty headers/body for the admitted request.
   - Require the request to retire with no redirect, retry, or inflight work.

4. **Preserve the previous commit**
   - Require unchanged URL, title, DOM, CSP, history/index, and HSTS.
   - Require broker navigation, provisional commit, and history state cleared.

### should recover through the bound broker worker protocol

1. **Render and retain the committed worker frame**
   - Initialize the worker through a capability-bound command.
   - Commit the stable page and capture its Draw IR frame.

2. **Bind the admitted navigation from worker to broker**
   - Send the replacement navigation through the worker protocol.
   - Require a bound document fetch for the failed URL.

3. **Dispatch one sanitized TLS failure through SBR2**
   - Have the broker emit a status-zero, empty response with the stable hostname
     failure.
   - Decode the bound response and require no private platform detail.

4. **Return a recoverable retained frame and keep both sides alive**
   - Require a successful worker result with the same composition revision and
     batches as the previously committed frame.
   - Require the stable failure in bounded diagnostics.
   - Accept the frame at the broker without changing URL, title, or history,
     then require a subsequent worker command to succeed.

Execution remains held until a source-matched admitted pure-Simple runtime is
available. Rust seed, bootstrap, or mock TLS output cannot promote this manual.
