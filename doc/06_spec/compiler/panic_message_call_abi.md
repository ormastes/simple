# Panic message call ABI

Authored manual for `test/01_unit/compiler/mir/panic_message_call_abi_spec.spl`.
This file was written by the developer; it is not generated docgen output.
The four MIR scenarios executed under the explicitly enabled Rust seed
interpreter (4 passed, 0 failed). Qualified native SSpec execution and native
validation of the changed producer are pending.

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
modes. The dynamic mode was added afterwards and has not yet executed. See the
[bug and evidence record](../../08_tracking/bug/cranelift_panic_call_abi_conflict_2026_10_30.md).
