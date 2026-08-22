# SimpleOS filesystem HTTP/1.1 incremental framing owner

## Problem

`src/os/apps/servers_user/main.spl` performs one 8192-byte receive and therefore
rejects otherwise valid HTTP/1.1 requests when headers or a declared body arrive
in multiple TCP fragments. Its retry send path also must slice after a short
write because `os.userlib.net.socket_send` has no source-offset/scatter-gather
operation.

## Required owner design

Implement a private/opaque per-connection framing owner. Callers may append
bounded byte fragments and obtain a complete/invalid/incomplete result, but may
not supply scalar resume offsets, cached Content-Length, line counters, or scan
frontiers. The owner must incrementally enforce request-line, header-line,
header-count, field-name token, control-byte, Content-Length, Transfer-Encoding,
and total-body limits before dispatch. It must retain `Connection: close` until
a complete keep-alive lifecycle is owned.

## Acceptance and performance bounds

- Accept headers and policy-valid bodies fragmented at every byte boundary,
  including a 10 MiB body delivered in one-byte successful reads.
- Count only consecutive no-progress receives against the retry allowance;
  successful reads are bounded by monotonic retained bytes.
- Reject forged/stale resume attempts by construction: no public resume-state
  constructor or scalar-resume API.
- Reject bare LF, embedded CR/control bytes, whitespace-before-colon,
  duplicate/conflicting Content-Length, TE+CL, malformed lengths, oversized
  unterminated lines, and empty initial lines.
- Scan and copy O(request bytes) total with O(policy buffer limit) peak retained
  memory. Never rescan or copy the accumulated header per fragment; a one-byte
  fragmented maximum header must remain O(H), not O(H²).
- Preserve the existing Pure-Simple parser/policy and filesystem server API.
- Add handler-level correctness tests plus timing and peak-RSS/allocation
  comparison using the admitted self-hosted runtime on x86-64, ARM64, and RV64.
- Do not invent a send-offset extern. Add it only through the canonical
  `os.userlib.net` syscall facade with separate ownership and evidence.

## Status

Open. A three-cycle implementation attempt was reverted after independent
review found the choice between forgeable public resume scalars and O(H²)
canonical prefix rescanning had not converged on an opaque O(H) owner. The
self-hosted runtime was unavailable, so runtime/performance evidence was not
produced.
