# MC/DC HAL captured device payload v1 evidence

REQ-015 now has one exact normalized payload/replay contract for captured
randomness, interrupt, MMIO, and DMA interactions. The parent authority owns
the only entropy/device effect and supplies a sealed capability/grant identity,
observation, and caller-owned byte region. Provider workers compare those
records and never receive a device handle or physical address.

## Safety and complexity

- Validation and scalar comparison are O(1).
- Exact byte comparison is O(payload bytes), one linear pass via caller-owned
  storage; there are no copies, heap allocations, system calls, or hardware
  effects.
- Payload capacity is fixed at 65,536 bytes and replay capacity/read-once tokens
  are fixed at 62. Sequence and token reuse fail closed with structured status.
- Exact comparison includes opcode, invocation/sequence, capability and grant,
  scalar semantics, structured observation/error status, interaction digest,
  region digest, length, and every caller-owned byte.

## Native evidence

The C self-check passed with `-Wall -Wextra -Werror -pedantic` plus AddressSanitizer
and UndefinedBehaviorSanitizer. A 10,000,000-iteration 32-byte exact-replay run
measured 27.228 ns/replay and 1,536 KiB peak RSS, with zero contract allocations.
The earlier unsanitized observation before the entropy authorization binding was
35.352 ns/replay at the same 1,536 KiB peak RSS; the final result is not a
regression.

The Pure Simple optimizer was not run because the deployed self-hosted compiler
is currently inadmissible; the Rust seed was not substituted and no full build
was retried.
