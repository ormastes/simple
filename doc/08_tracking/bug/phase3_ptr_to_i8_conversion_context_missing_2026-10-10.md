# Phase 3 rejects ptr-to-i8 without enough value context

Status: **OPEN**. Diagnostic source correction drafted; root cause and
corrected-producer execution remain unproven. Do not relax pointer casts.

## Original failure

Producer `/dev/shm/simple-phase2-latest-ord-20261010/build/simple`, source
`a0e3b4ff2b7aa8e3d4b7c9accc83bfc8c897dbf4`, compiled frozen source
`b9ccb2ab9c86017724f29e5a2985dfe9b25d60dd`. The requested entry was
`src/app/cli/shard_mem_clamp.spl`; its 29-module closure reached
`lib.common.crypto.secure_memory` during native codegen and rejected:

```text
panic: compile error: unsupported LLVM value conversion from ptr to i8
```

The retained receipt and command are under
`/home/ormastes/simple-phase3-1159-object-attempt-20261010/adaptive-epoch/row-0022/`.
`build.log` SHA-256 is
`6e686c84e2d0c998b4f844f4059627d69da147576aca623b741bba4df273a347`.
Exit was 1, no object. `SIMPLE_BOOTSTRAP=1` selected the explicitly reported
bootstrap-flat route; this was not full-MIR qualification of the closure.
The progress module is not sufficient proof of the emitting function/value.

## Narrow evidence

The same pure-Simple producer ran normal AOT with `SIMPLE_BOOTSTRAP` and
`SIMPLE_BOOTSTRAP_DEBUG` unset, private caches, LLVM, threads=1, and
`--entry-closure --emit-object`. Evidence directory:
`/home/ormastes/simple-astra-cast-evidence-20261010/`.

* `byte-normal.log` / `byte-normal.o`: exit 0, 936-byte ELF; `readelf -Ws`
  confirms a 58-byte `__simple_main` and an extern reference to
  `rt_array_set_len_known`. The retained nearby fixture is
  `test/fixtures/compiler/llvm_i8_extern_result_probe.spl`. Object generation
  passed; the executable has not been linked/run, so exit 42 remains a gate.
* `secure-normal.log` / `secure-normal.o`: exit 0, 5088-byte ELF with all eight
  real function symbols, including `secure_set_u8_length` (21 bytes) and
  `secure_zero_u8_range` (365 bytes). The source was a byte-identical copy of
  `secure_memory.spl` relocated to `astra_secure_probe.main`; no imported
  29-module context was present. This is source-isolation evidence, not proof
  that the original closure passes or that all runtime semantics are correct.

These results reject a blanket claim that an i8 extern or this source always
requires ptr-to-i8 coercion. They do not establish whether the original cause
is HIR typing, MIR transport, call signature, or backend load selection.

## Diagnostic correction and next gate

`core_codegen.spl::emit_value_type_conversion` restores `function=... value=...`
to the existing rejected-conversion message. It preserves the original prefix,
unsupported-pair rejection, and cast selection. This context was present in the
historical evidence in
`bootstrap_flat_llvm_receiver_signature_corruption_2026-08-16.md`.

After rebuilding a frozen producer containing the diagnostic, replay the exact
original closure once and retain function, SSA value, its defining MIR
instruction, declared source type, and expected parameter/store/return type.
Repair the first incorrect boundary and execute both the minimal failure and
the nearby legal byte-result fixture. Missing rebuilt-producer evidence is not
PASS. Do not use `SIMPLE_BOOTSTRAP_DEBUG=1` to obtain this evidence: see
`mir_to_llvm_bootstrap_debug_changes_translation_semantics_2026-07-13.md`.
