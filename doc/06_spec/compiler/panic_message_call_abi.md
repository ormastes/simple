# Panic message call ABI

Authored manual for `test/01_unit/compiler/mir/panic_message_call_abi_spec.spl`.
This file was written by the developer; it is not generated docgen output.
The four MIR scenarios executed under the explicitly enabled Rust seed
interpreter (4 passed, 0 failed). The changed producer also passed all four
native fixture modes with clean build diagnostics. Qualified native SSpec
execution and generated docgen output remain pending.

| Scenario | Steps and required result |
| --- | --- |
| Dynamic message and Abort | Emit one message-producing call, then a one-operand panic. Require one producer, one byte-data read and one byte-length read of the same local, a two-argument panic signature, and the retained Abort terminator. |
| Explicit raw bytes | Emit pointer plus length for bytes containing NUL. Require the existing two arguments and full length to remain unchanged. |
| Unrelated function | Emit an ordinary one-argument call. Require no additional calls or argument rewrite. |
| Malformed panic arity | Emit three panic arguments. Require the invalid shape to remain visible to its existing validator. |

The companion native fixture is
`test/fixtures/compiler/panic_abi_conflict_probe.spl`. A changed producer must
compile it without rejected declarations, missing imports, or zero function
references. Then execute each mode separately:

- Default: exit0, stdout exactly `PANIC_ABI_SUCCESS` plus newline, empty stderr.
- `--explicit`: nonzero, stdout empty, stderr containing the explicit panic marker;
  no fallthrough marker.
- `--cast`: nonzero with the intended type-mismatch panic; a bare illegal
  instruction is a failure, even though it prevents fallthrough.
- `--dynamic`: nonzero, stdout exactly `PANIC_ABI_MESSAGE_EVALUATED` plus newline,
  stderr exactly `panic: panic-abi-dynamic--dynamic` plus newline. The runtime
  argument participates in concatenation; evaluate its message producer once
  and retain the tagged text until pointer/byte-length extraction. No fallthrough.

The initial native fixture reproduced the ABI conflict with literal and cast
modes. Candidate `cef67a241aae27c9a98839158fd88255ce15f140dc79e8efeee565252a28ce0a`
subsequently passed all four native modes: default exit0, explicit/dynamic/cast
exit1 with their expected messages, dynamic producer marker exactly once, no
fallthrough or SIGILL. Its separate full CLI matrix exceeded the enforced RSS
cap and remains unqualified; this is scoped native regression evidence. See the
[bug and evidence record](../../08_tracking/bug/cranelift_panic_call_abi_conflict_2026_10_30.md).
