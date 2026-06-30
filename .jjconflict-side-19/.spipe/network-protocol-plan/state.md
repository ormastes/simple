# SStack State: network-protocol-plan

## Status: CLOSED — 2026-05-20

## User Request
> next task from the plan — network_protocol_plan (P1 TLS KeyUpdate/NewSessionTicket, P2 HTTP/3 frame layer/WS deflate/auth retry, P3 STUN/SCRAM-SHA-512)

## Task Type
feature

## Refined Goal
> Implement remaining network protocol modules: TLS 1.3 KeyUpdate and NewSessionTicket post-handshake messages, HTTP/3 frame layer with QPACK header compression model, WebSocket permessage-deflate extension, STUN binding request/response, and SCRAM-SHA-512 extension.

## Acceptance Criteria
- [x] AC-1: TLS KeyUpdate — KeyUpdateRequest message type, key re-derivation from existing traffic secrets, update_requested/not_requested distinction
- [x] AC-2: TLS NewSessionTicket — ticket structure with lifetime/age_add/nonce/extensions, server emission model, client PSK storage entry
- [x] AC-3: HTTP/3 frame types — H3FrameType enum (DATA/HEADERS/CANCEL_PUSH/SETTINGS/PUSH_PROMISE/GOAWAY/MAX_PUSH_ID), frame header parsing model
- [x] AC-4: QPACK header compression — static table entries, encoder/decoder instruction model, required insert count, base delta
- [x] AC-5: WebSocket permessage-deflate — extension negotiation parameters (server/client_no_context_takeover, max_window_bits), compression/decompression frame model
- [x] AC-6: HTTP Basic+Digest completion — DigestChallenge with realm/nonce/qop/opaque, response hash computation model, retry logic
- [x] AC-7: STUN binding — StunMessage with type/length/magic_cookie/transaction_id, binding request/response/error, MAPPED-ADDRESS attribute
- [x] AC-8: SCRAM-SHA-512 — extend SCRAM model with SHA-512 hash function, salted password derivation, server/client proof
- [x] AC-9: Protocol registry — ProtocolModule with name/rfc/status/test_status for tracking all 18 modules
- [x] AC-10: Verification spec — 20 tests covering KeyUpdate, NewSessionTicket, H3 frames, QPACK, WS deflate, STUN, SCRAM-512, registry

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [x] 5-implement (Engineer) — 2026-05-18
- [x] 6-refactor (Tech Lead) — 2026-05-18
- [x] 7-verify (QA) — 2026-05-18
- [x] 8-ship (Release Mgr) — 2026-05-18

## Phase Outputs

### 1-dev
10 ACs across P1/P2/P3. Existing: src/os/tls13/, src/os/http/, WebSocket frame layer, SCRAM-SHA-256, JWT, PASETO, SOCKS5.

### 5-implement
5 parallel Sonnet agents. 4 source + 1 test:
- src/os/tls13/tls_post_handshake.spl — KeyUpdateRequest + KeyDerivation + NewSessionTicket + PskStorageEntry
- src/os/http/http3_frame.spl — H3FrameHeader + H3Settings + QpackStaticEntry + QpackDecoderState
- src/os/http/ws_deflate_auth.spl — WsDeflateParams + WsCompressedFrame + DigestChallenge + DigestResponse
- src/os/http/stun_scram.spl — StunMessage + ScramSha512 + ProtocolModule + ProtocolRegistry
- test/01_unit/os/net_protocol_spec.spl — 20 tests

### 7-verify
20/20 tests PASS.
