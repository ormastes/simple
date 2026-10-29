# Mixed panic ABI declarations produce zero function references

Status: implemented; MIR diagnostic regression passes; changed-producer native validation pending.

The C runtime requires `rt_panic(raw_bytes_pointer, byte_length) -> void`.
Generated MIR guards and builtin panic/assert supplied one text operand while
text code-point casts supplied two. A module containing both declarations could
refuse the second declaration, import handle zero, and omit the panic call.
Its following Abort still traps, but the intended panic diagnostic is lost.

`MirBuilder.emit_call` now expands exactly a one-argument `rt_panic` into the
existing pointer/byte-length ABI. It reuses the evaluated operand for
`rt_string_data` and `rt_string_len`; Move operands become Copy references to
that same local. Existing two-argument calls, unrelated calls, malformed arity,
and caller-owned Abort terminators are unchanged. Builtin panic keeps tagged
text until this split rather than first erasing its stored length via
`rt_interp_cstr`. The C panic formatter remains C-string based, so embedded NUL
may truncate printed diagnostics even though the correct byte length is passed.

## Observed native red

Producer SHA256: `ca2e62284198137f01cb99f32b6dcd530647ce587ed29bfc102ba5477f5411b3`.
It is a linked but canonically rejected P2, used only as an explicit diagnostic.
The durable fixture is `test/fixtures/compiler/panic_abi_conflict_probe.spl`.
Build exit0 still logged a conflicting `(i64,i64)->i64` declaration against
`(i64)->i64`, then missing declared function and missing func-ref handle0.
Default mode exited0 with `PANIC_ABI_SUCCESS`; `--explicit` exited1 with its
marker; `--cast` exited132 with Illegal instruction instead of the expected
code-point type-mismatch panic. None of these results qualifies clean codegen.

Evidence directory:
`/work/native-hello-diagnostic-20261030/panic-abi-probe/attempt-executable-copy/`.
Build log SHA256: `548f3564d0a8351dc5c4b9e9f43424c137b17a14369d4095346b12a18e112234`.
Artifact SHA256: `1713cead08705096495e6f8edb71e1850524d13e847887e1c21cbe5ffe2f2fe2`.
An earlier setup attempt failed127 before compilation because the immutable
artifact copy was not executable; the corrected run used a separate identical
0555 copy and retained the original 0444 evidence.

## MIR regression and remaining admission

`test/01_unit/compiler/mir/panic_message_call_abi_spec.spl` executed four tests,
4 passed / 0 failed, exit0, through the explicitly enabled Rust seed interpreter.
It checks the dynamic producer is emitted once, pointer and byte length reuse
its local, known ABI and Abort survive, explicit embedded-NUL byte length is
unchanged, and unrelated/invalid calls are not normalized. This is structural
source diagnostic evidence, not a qualified native Simple test run.
Log: `/private/tmp/astra-panic-abi-spec-ready.log`, SHA256
`ab0e79dc790ea03724fc1254325b3f1c6651476198ba5f138520407728141dc8`.

Native validation must rebuild the changed producer, compile the durable probe
without any declaration/import/zero-reference diagnostic, and execute all
three modes. The cast must report its intended panic, not merely exit nonzero.
Rerun the Linux capacity ABI probe with similarly clean compiler diagnostics
before treating its earlier successful execution as clean worker qualification.
Generic Cranelift Unit-return policy and failure latching are separate open
issues: build exit0 alone does not prove every emitted call survived.
