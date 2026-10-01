# Typed Bounded HAL Environment Extraction and Replay

Purpose: verify typed instruction extraction, sealing, deterministic replay, and failure on trace divergence. Audience: environment executor and HAL-provider maintainers.

Source: `test/03_system/runtime/hal_environment_replay_spec.spl`  
Evidence class: host fixture  
Current execution status: **PENDING/BLOCKED** — no admitted self-hosted compiler is available; no physical IRQ/MMIO/DMA execution is claimed.

## Preconditions

The executor receives a versioned operation, invocation, sequence, capability, argument/result region, deadline, and fixed instruction capacity. Replay must not repeat the physical effect.

## Operator workflow

1. Build the controlled environment fixture.
2. Extract ordered typed instructions into caller-owned storage.
3. Seal and capture the plan receipt.
4. Replay under another isolated provider.
5. Inject reorder, duplicate, overflow, changed opcode, or changed observation.
6. Verify structured divergence and no commit.

## Scenarios

- Ordered file and clock accesses seal into a complete trace.
- Reordered, duplicate, or overflowing accesses preserve the accepted prefix and fail closed.
- Exact replay completes without a second physical effect.
- Changed, extra, missing, or malformed evidence produces divergence.

## Acceptance boundary

The fixture exercises production extraction/replay contracts. Real file, stream, process, environment, clock, random, socket, interrupt, MMIO, and DMA acceptance remains per-adapter evidence. Unavailable hardware may only be `EXCLUDED` by a fresh governed reason; it is never promoted to PASS.

## Traceability

REQ-015 through REQ-018; NFR-005 through NFR-010 as applicable.

## Executable source

The complete executable source remains in `test/03_system/runtime/hal_environment_replay_spec.spl`.
