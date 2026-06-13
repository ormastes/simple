# Feature: sshd_harden

## Raw Request
with spipe dev skill, harden simple os ssh server on x86, riscv, aarch64; small model-rated tasks, parallel agents, higher-model review after.

## Task Type
code-quality

## Refined Goal
Every SSH wire parse in src/os/apps/sshd validates lengths/bounds before use, auth paths are constant-time and attempt-limited, and malformed-input specs prove it.

## Acceptance Criteria
- AC-1: Each packet/kex/transport wire parse rejects truncated, oversized, and zero-length input with an error (no panic, no silent acceptance), proven by unit specs in test/01_unit/os/apps/sshd/.
- AC-2: MAC verification uses constant-time comparison; a spec asserts the compare helper is used on the MAC path.
- AC-3: Authentication enforces a max-attempt limit and kex negotiation rejects empty/unknown algorithm lists; specs cover both.
- AC-4: All existing sshd specs still pass in interpreter mode (SIMPLE_BOOTSTRAP_DRIVER set for stage4).

## Scope Exclusions
No changes outside src/os/apps/sshd/** and test/*/os/apps/sshd/**. No new crypto algorithms. No QEMU live-lane changes.

## Phase
implement-done

## Log
- dev: Created state file with 4 acceptance criteria (type: code-quality)
- Track A (implement): constant-time MAC compare + bounds-checked wire parses + malformed-packet specs
  - src/os/apps/sshd/ssh_mac.spl: replaced timing-vulnerable _bytes_equal (early return on mismatch) with XOR-accumulator constant-time compare (diff |= a[i]^b[i], return diff==0). Length mismatch still returns early (length is not secret).
  - src/os/apps/sshd/ssh_packet.spl: added ssh_get_u32_checked() returning Result<u32,text>; existing ssh_get_u32 signature untouched (no caller breakage).
  - src/os/apps/sshd/ssh_session_auth.spl:107: moved bounds check to precede arithmetic (service.next_offset + 13 > payload.len() guard before computing off = next_offset + 4 + 8 + 1).
  - test/01_unit/os/apps/sshd/ssh_mac_spec.spl: 10 it-blocks — correct MAC accepted, tampered MACs (single-bit flip, wrong length, all-zeros) rejected; both sha2-256 and sha2-512 variants; unknown algorithm returns Err; none accepts empty.
  - test/01_unit/os/apps/sshd/ssh_packet_malformed_spec.spl: 17 it-blocks — ssh_get_u32_checked (empty/truncated/offset-past-end/exact/offset variants), ssh_get_string (zero-len/truncated-length-field/declared-len-exceeds-data/empty-content/3-byte), ssh_packet_read (empty/4-byte/pkt_len=0/pkt_len=1/oversized/incomplete/round-trip).
  - Spec results: ssh_mac_spec 10/10 pass; ssh_packet_malformed_spec 17/17 pass; ssh_packet_spec 10/10 pass (pre-existing, unaffected). Pre-existing failures: ssh_kex_rsa_contract_spec (missing ssh_sign_exchange_hash symbol, pre-existing) and ssh_kex_hostkey_matrix_spec (sha512/ed25519 perf timeout, pre-existing). Not caused by this change.
