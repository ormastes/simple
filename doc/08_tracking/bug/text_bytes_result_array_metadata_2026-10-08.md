# Text bytes result loses runtime-array metadata

Status: **UNQUALIFIED source repair**, pending a coordinated compiler rebuild
and actual native regression execution. No application pass is claimed.

The qualified Phase2 compiler
`15a04a74f55062bed6767a9ebfc7a917035685b8a0f103144eb3e1673f09a86d`
built the Cranelift encoding fixture from source
`aa66f6eb33e3e8e8d9eb2aa2b591c54bae135494`, but its executable exited 2:
the facade's ASCII result had length zero instead of six. Retained evidence:
`D:/dev/simple/build/item5-scalar-apps-20261008/facade-cranelift-encoding/`
and `D:/dev/simple/build/review/item5-cranelift-array-len-20261008/`.

## Actual boundary evidence

- `rt_string_bytes` received correctly tagged Cranelift text and returned a
  separate tagged array with length six (root's retained diagnostic log).
- The facade calls through GOT `0x91d0` at ELF offset `0x30b9`; its relocation
  resolves to `rt_string_len` at `0x4d40`, even though the receiver is that array.
  Zero string length skips the copy loop and returns the initially empty output.
- GDB then observed the caller's `rt_len` input: an array header of 2, length
  zero, capacity four. `rt_len` correctly returned zero. The length accessor
  itself is not defective.
- The unused copy-loop body also emitted direct pointer arithmetic on the
  tagged `raw` handle, exposing the same lost array representation for indexing.

## Source cause and repair

The proven-text `bytes()` builtin in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` emits
`rt_string_bytes` with its raw i64 ABI return and immediately returns that
local. It omitted the array metadata used by other collection-producing
builtins. The unresolved `len` fallback subsequently changes `rt_len` to
`rt_string_len` when `local_is_runtime_array` cannot prove an array.

Keep the runtime ABI and the existing exact text-receiver guard. Mark the
result as a runtime array and tagged runtime value, record U8 element decoding,
and remember the HIR `Array(Int(8, false))` type. The runtime produces tagged
integer word slots, not packed bytes or a borrowed text pointer. This metadata
also selects array access for indexing and survives normal local/alias
metadata propagation. No facade workaround, runtime change, or name-only
custom-method interception is introduced.

`test/fixtures/compiler/text_bytes_result_metadata.spl` checks empty, ASCII,
multibyte/astral UTF-8, embedded NUL, inferred aliases, indexed bytes, for-in
sum, chained length, and a custom same-named method. It has not yet executed.
The prior facade fixture must also pass on the repaired compiler. LLVM's
independent raw text-literal defect must be repaired separately before an LLVM
result can qualify the complete text path; this diagnosis used Cranelift.
