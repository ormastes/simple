# host_identity_private_use_v1 leaves seed material unwiped (2026-11-18)

Status: OPEN. Found by the opus review of milestone_0030 PR-1a (P2-3). The behaviour predates PR-1a, but PR-1a
puts this parser on the controller signing path (`host_identity_private_sign_{grant,approval}_v1`).

`src/app/orchestrator/host_identity_key_v1.spl`, `host_identity_private_use_v1`:
- The early format/consistency refusals return before `raw` and `seed` are wiped. Only the success and
  signing-refusal returns wipe them.
- The text copies `source`, `encoded_lines` and `encoded` hold the base64 private section and are never wiped.
  Text is immutable, so a `[u8]` wipe cannot reach them.
- `pair.0`, the expanded private key from `pure_ed25519_keypair_from_seed`, is never wiped.
- If the caller's `bytes = value` copies the array, the buffer left in `read.bytes` is not wiped
  (`controller_authority_store_read_v1`).

Fix: use a single exit path that wipes `raw`, `seed` and `pair.0`, and parse the PEM armour and base64 by slicing
`[u8]` directly instead of going through `bytes_to_text`.
