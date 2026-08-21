# Feature: SimpleOS web and SSH protocol hardening

## Raw Request
Audit and implement missing production protocol owners for Simple web server and SSH/SSHD: TLS HTTP/1.1+H2, WebSocket where promised, HTTP3/QUIC/WebTransport only if required/architecture exists; SSH auth/channel/SFTP live path. Avoid claiming protocols not implemented; implement highest-priority concrete missing paths and real loopback/live acceptance. Check duplication/perf.

## Task Type
feature

## Refined Goal
Make the existing Simple web and SimpleOS SSH daemon production entrypoints expose only implemented protocol capabilities and prove their highest-priority HTTP/TLS/WebSocket and SSH authentication/channel/SFTP paths over real bounded transports.

## Acceptance Criteria
- AC-1: The canonical protocol requirements and architecture are audited against production entrypoints; HTTP/3, QUIC, and WebTransport remain explicitly unavailable unless their complete required owner stack and live evidence exist.
- AC-2: The production web server negotiates TLS ALPN honestly, serves HTTP/1.1 and HTTP/2 through their canonical owners, and rejects malformed, oversized, timed-out, or unsupported protocol input with bounded state.
- AC-3: Every production WebSocket capability that is advertised performs a standards-valid upgrade and bounded frame/message lifecycle over a real loopback transport, including rejection coverage.
- AC-4: The SimpleOS SSH daemon production path performs host-key exchange, supported user authentication, session-channel lifecycle, command execution, and SFTP subsystem dispatch through canonical owners without fixture-only bypasses.
- AC-5: Fresh live/loopback acceptance proves positive and adjacent rejection cases for the reachable web and SSH paths; unavailable QEMU-only or external-host rows remain explicit blockers with exact resume commands rather than PASS.
- AC-6: Touched Simple sources pass focused syntax/check and behavioral tests, direct-environment guards, token duplication review, and a bounded performance/resource review without new raw runtime hooks or per-OS app duplication.
- AC-7: Knowledge is refreshed in the affected requirements/architecture/design/plan, `doc/07_guide`, feature- and layer-expert wiki skills, generated/manual spec evidence where changed, and every unfixed gap has a `doc/08_tracking/bug` record with file/line and unblock condition.

## Scope Exclusions
Implementing or advertising HTTP/3, QUIC, or WebTransport without the architecture-mandated end-to-end transport, recovery, flow-control, QPACK, backpressure, and close owners; replacing Simple protocol owners with host-only external servers; unrelated bootstrap work.

## Cooperative Review
Parallel umbrella lanes are coordinated by the parent task. This lane owns `ProtocolCapabilityManifestV1`, HTTP TLS/ALPN/WebSocket production owners, SSH authentication/session/SFTP owners, `step_web_protocol_live`, `step_ssh_protocol_live`, `check_web_protocol_live.shs`, and `check_ssh_protocol_live.shs`. Any scaffold must fail with `assert(false)` or `fail(...)`. Merge owner and final highest-capability reviewer: parent agent; generated-manual reviewer: this lane followed by parent review.

## Phase
dev-done

## Log
- dev: Created state file with 7 acceptance criteria (type: feature).
- impl: Rejected unknown/H3 TCP ALPN without H1 downgrade and rejected duplicate SFTP initialization; recorded the unavailable SFTP VFS/live path and stale QEMU gate.
- audit: Confirmed production HTTP/SSH do not yet publish `ProtocolCapabilityManifestV1`; retained this as an explicit open blocker rather than inferring support from source modules.
