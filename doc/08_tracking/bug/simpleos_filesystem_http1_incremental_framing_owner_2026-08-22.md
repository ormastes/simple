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

Implemented in the filesystem server lane with a module-private
`Http1RequestFrameOwner`. The exported socket operation owns construction,
incremental scanning, and terminal delivery; no resume scalar or constructor
crosses the module boundary. Each framing/header byte is appended and examined
once, body tails are bounds-checked and bulk-appended once per receive, each
completed header line is materialized once, and the full request is
materialized once at delivery. Peak retained framing state is bounded by the
configured request-line, header, and exact 10 MiB body policy.

Static correctness and performance-structure coverage is in
`test/01_unit/os/apps/servers_user/http1_request_frame_owner_spec.spl`.
Runtime timing/RSS and x86-64/ARM64/RV64 execution evidence remain pending
because this worktree has no admitted self-hosted `bin/simple`; the Rust seed
was not used as a substitute.
