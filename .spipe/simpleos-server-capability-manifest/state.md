# Feature: simpleos-server-capability-manifest

## Raw Request
Wire the SimpleOS server protocol capability manifest into actual web/sshd startup and negotiation so advertised protocols exactly match reachable implementations; unsupported HTTP/3, QUIC, and WebTransport must fail closed, while HTTP/1.1, HTTP/2, WebSocket, SSH, and SFTP reporting is hardened without duplicating protocol stacks. Add specs, manuals, docs, wiki, and bug tracking.

## Task Type
bug

## Refined Goal
Make the canonical SimpleOS web and SSH startup paths derive every advertised and negotiated protocol from owner-issued `ProtocolCapabilityManifestV1` evidence so only reachable implementations are claimed and unsupported protocols are rejected.

## Acceptance Criteria
- AC-1: Claim the tracked unwired-manifest bug before source edits and preserve a pre-fix reproducer showing startup/negotiation can claim a protocol without an owner-issued reachable manifest.
- AC-2: The pure-Simple web and SSH owners issue and consume one canonical capability set at startup; no second HTTP, WebSocket, SSH, or SFTP implementation is introduced.
- AC-3: HTTP/1.1, HTTP/2, and WebSocket are advertised only when their existing reachable startup/dispatch implementation and required transport/profile evidence are present; unsupported negotiation fails closed.
- AC-4: SSH and SFTP are reported independently: SSH requires the reachable daemon/session owner and SFTP requires the reachable authenticated subsystem owner; dead client SFFI externs are not evidence.
- AC-5: HTTP/3, QUIC, and WebTransport are never advertised or accepted until their end-to-end transport owners satisfy the manifest; explicit probes and adjacent unknown-protocol cases reject them.
- AC-6: Executable SSpec scenarios trace these criteria and the mirrored manual is understandable without source; focused unit/source-contract checks cover exact and adjacent regressions.
- AC-7: Update affected research/requirements/architecture/design/plan, `doc/07_guide`, generated/manual `doc/06_spec`, feature and layer expert wiki pages, and the claimed bug record; file every newly found unfixed gap with file:line and unblock condition. Workflow/skill/command docs are N/A because product capability behavior, not SPipe workflow, changes.
- AC-8: Focused checks, lint/duplication gates, direct-env audits, and spec-layout audit pass once; at most three distinct fix/verify cycles.

## Scope Exclusions
Implementing QUIC, HTTP/3, WebTransport, new TLS/ALPN stacks, or new SSH/SFTP stacks; release, commit, and push.

## Cooperative Review
N/A: the parent assigned this bounded implementation lane to one agent; canonical shared names are `ProtocolCapabilityManifestV1` and the existing web/sshd startup owners, and no sidecar delegation was requested.

## Phase
dev-done

## Log
- dev: Created state file with 8 acceptance criteria (type: bug).
- research/design/implement: Added the canonical reachability adapter, wired
  HTTP TLS/startup and SSH startup, and added unit/system/manual/doc/wiki
  artifacts without adding protocol stacks.
- verify cycle 1: BLOCKED before execution because this worktree has no
  admitted `bin/simple`; exact resume commands are in the tracked bug. Static
  source and layout checks remain available.
- architecture hardening: Removed bind-time SSH/SFTP self-claims. Live session
  auth/channel/SFTP facts now feed a private evidence-owner handle and a
  generation/sequence/authority-bound single-use publisher; stale, replayed,
  foreign, unauthenticated, and channel-less handles reject. HTTP derives
  cleartext/TLS facts from config and publishes H2 only after a worker-issued
  successful negotiation message. Negative tests and manuals were refreshed.
- final evidence hardening: TCP connect/close and TLS ALPN no longer authorize
  HTTP publication. Only a worker-completed H1 request/response emits cleartext
  or TLS1.2/certificate/AES evidence; H2 remains unpublished without equivalent
  full request/response evidence. SFTP stays unpublished despite subsystem-open
  evidence until a per-principal atomic VFS capability exists.
