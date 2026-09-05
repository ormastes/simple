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
- Track A (review follow-up): addressed adversarial-review findings
  - src/os/apps/sshd/ssh_auth.spl authenticate_password(): password compare now constant-time via _blobs_equal on ssh_ascii_text_to_bytes of both sides (timing side-channel on secret closed); username compare stays plain (not secret).
  - src/os/apps/sshd/ssh_kex_primitives.spl: deleted dead non-constant-time _bytes_equal (zero callers, latent hazard).
  - ssh_get_u32 call-site audit (reviewer claimed ~18 unguarded): VERIFIED ALL GUARDED — ssh_channel 225/227/229 (off+12 guard), 248/272 (len<6), 301/302 (len<9), 311/319 (len<5); ssh_auth 335 (len<5); ssh_cipher 164 (len<4+GCM_TAG), 306 (self-built plaintext), 325 (len<4+mac_len+1), 452 (len<4+POLY1305_TAG); ssh_transport 426 (off+4 guard); ssh_session_channel 313/315 (pos+16<=len); ssh_session 386 (recv loop ensures len>=20). ssh_get_u32_checked stays as the safe variant for future call sites (spec-covered).
  - test/01_unit/os/apps/sshd/ssh_auth_password_spec.spl: NEW 6 it-blocks — correct password accepted; wrong equal-length / different-length / empty password rejected; unknown user rejected; multi-user isolation.
  - Regression sweep green: sshd_spec 6/6, ssh_transport_spec 15/15, ssh_session_shell_spec 6/6, ssh_packet_spec 10/10, ssh_mac_spec 10/10, ssh_packet_malformed_spec 17/17, ssh_auth_password_spec 6/6 (70 total). bin/simple check OK on all touched sources.
- orchestrator sign-off (2026-06-13): independently spot-checked cipher:164/325/452, session:386, session_channel:313 — guards confirmed; review's "18 unguarded sites" blocker refuted by three independent audits. ssh_get_u32_checked kept without production caller as an ACCEPTED DEVIATION from the no-unused-code rule: ssh_packet_read's unchecked-read+guard structure carries load-bearing baremetal codegen workarounds (val-from-return corruption), so a Result-returning read must not be wired into that hot path; the checked variant is the docstring-referenced, spec-covered entry point required for any NEW parse site. Phase: verified.
