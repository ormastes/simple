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
and UndefinedBehaviorSanitizer. A 50,000,000-iteration 32-byte exact-replay run
measured 23.340 ns/replay and 1,536 KiB peak RSS, with zero contract allocations.
The earlier 10,000,000-iteration baseline before structured observation
validation was 35.352 ns/replay at the same 1,536 KiB peak RSS. Validation is
therefore included without a measured regression. The Pure Simple cursor also
uses a validated internal comparison path, avoiding duplicate validation of
both payloads on every replay.

The Pure Simple optimizer was not run because the deployed self-hosted compiler
is currently inadmissible; the Rust seed was not substituted and no full build
was retried.

## Parent-authoritative three-provider comparison

`HalDeviceCompareOwnerV1` now owns three fixed Pure/C/Rust result slots and
three independent read-once cursors. Providers receive only a sealed captured
payload plus caller-owned byte regions; the parent alone validates and commits.
Entropy, IRQ acknowledge, MMIO read, and DMA poll parity vectors prove that
validation never repeats the physical interaction. Duplicate publication and
out-of-policy providers fail closed.

- alpha: all three providers are required and any difference blocks commit;
- beta: all three are required, but a validated preferred result may commit;
- normal: only the configured preferred provider slot executes;
- hot path: O(payload bytes), one byte pass, fixed slot state, zero heap
  allocations/copies/device calls.

Native C/Rust parity passed exact four-kind vectors with
`parity_mask=7 effects=0 allocations=0`. On this host the unchanged C replay
baseline measured 38.204 ns/replay and 1,536 KiB peak RSS. After the owner
addition the same replay measured 37.063 ns/replay (-3.0%, noise/improvement),
while the three-slot owner measured 55.294 ns/provider across 30,000,000
validations at the same 1,536 KiB peak RSS. The independent Rust validator's
final parity run measured 44.084 ns/replay and 1,792 KiB peak RSS across
10,000,000 iterations.
The Simple optimizer remains unavailable for the same inadmissible compiler
reason; no Rust-seed substitution or full build was used.
