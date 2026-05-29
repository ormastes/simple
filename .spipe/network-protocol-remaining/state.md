# network-protocol-remaining

## Status: CLOSED — 2026-05-20
All ACs complete: TLS KeyUpdate, QPACK encoder/decoder, STUN binding all implemented. Phase 8-ship delivered.

## Phase: 8-ship

## Type: feature

## Goal
Implement remaining network protocol modules: TLS KeyUpdate (RFC 8446 section 4.6.3),
QPACK encoder/decoder (RFC 9204 section 4), and STUN binding (RFC 8489).
HTTP/3 frame layer and WS permessage-deflate are already implemented.

## Acceptance Criteria
- [x] AC1: TLS KeyUpdate message parse+emit with key re-derivation hook (`src/lib/nogc_sync_mut/tls/key_update.spl`)
- [x] AC2: QPACK encoder — prefixed-integer encode, literal/indexed header field instructions (`src/lib/nogc_sync_mut/http/h3/qpack_encoder.spl`)
- [x] AC3: QPACK decoder — prefixed-integer decode, instruction dispatch (`src/lib/nogc_sync_mut/http/h3/qpack_decoder.spl`)
- [x] AC4: STUN binding request/response — message header, attribute TLVs, XOR-MAPPED-ADDRESS (`src/lib/nogc_sync_mut/net/stun.spl`)
- [x] AC5: All new files pass syntax check (`bin/simple build lint`)

## Audit Notes
- `src/lib/nogc_sync_mut/http/h3/h3_frame.spl` — already done (HTTP/3 frame layer)
- `src/lib/nogc_sync_mut/http/h3/qpack_static.spl` — already done (static table)
- `src/lib/nogc_sync_mut/http/ws/permessage_deflate.spl` — already done
- Plan doc `src/os/` paths are stale; actual layout is `src/lib/nogc_sync_mut/`
