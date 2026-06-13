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
dev-done

## Log
- dev: Created state file with 4 acceptance criteria (type: code-quality)
