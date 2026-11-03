# Typed optional stdin text equality handles raw and tagged strings

Status: FIXED (P1, scoped source/ABI repair) — representation-aware typed-text equality is wired through MIR, runtime ABI, and interpreter extern adapter and passed focused owner tests and a bounded C selfcheck.

## Failure and scoped repair

The original typed optional stdin consumer compared raw text returned by the C
stdin reader with a tagged string literal through `rt_native_neq`. The native
plugin consumer failed at `loaded LLVM identity token mismatch` before its 19
downstream checks, even though its identity receipt said the actual DLL
identity was verified. The source/ABI repair wires the existing
`rt_text_eq_any(i64, i64)` helper through the runtime symbol registry and
interpreter extern adapter, and lowers
statically typed `String` equality and inequality through the
representation-aware helper. It preserves the existing paths for `is`, `Any`,
and non-String operands.

This FIXED status is limited to that typed-text equality source/ABI boundary.
The 31-check end-to-end language fixture was not run, and no seed rebuild or
plugin consumer qualification is claimed. A later plugin route has a separate
`Some` wrapper failure; it remains outside this repair. No JIT tuple getter,
Cranelift, CLI, Phase 2, or Phase 3 claim is made.

## Focused evidence

Validation receipts below are under
`C:/dev/p3new/typed_text_equality_20261103/validation_01/`. The tracked source
patch is `source_patch_tracked.diff` with the SHA-256 recorded below.

Source patch SHA-256:
`F7025E6ED499420713692BBF9968F750D60D226B04F375629662716D6A84CFCF`; pinned
source head `4fccb94e564b25a0a2effdd711113da5a1b1e20c`, source pin SHA-256
`AF9951BA38E5EF254DF758C87F352C39DC4082F36053201EB078BA2E802EC04D`.

Two unique Rust owner tests passed:

- MIR lowering routes statically typed String equality through the
  representation-aware runtime call. It passed in
  `validation_01/unit_attempt_01/result.sdn`, SHA-256
  `C361A4883BD8EE4F93D5CD0269A407526F7E1A77D40FBC019C4122714A3458AB`.
- The interpreter extern adapter selector was not selected in the initial
  run; the corrected exact-test continuation passed in
  `validation_01/unit_selector_continuation_01/result.sdn`, SHA-256
  `173D9EE23CE8F1E469B8F6CFC1964C1E67940FA33544F74E2E873FB60DB56EBC`.

The initial standalone C selfcheck link failed because required runtime
providers were omitted. That failed receipt is preserved at
`validation_01/c_selfcheck_attempt_01/result.sdn`, SHA-256
`203D4D7765F4A12E8D6F45339E79BF453615A5CFE1FA887B633077254882C458`. The
corrected private archive selfcheck then passed all 10 of 10 probes, with no
provider stubs and without a full runtime rebuild. Its result is
`validation_01/c_selfcheck_attempt_02/result.sdn`, SHA-256
`72C1DFC3896AB61A195DF0F4042327196B8A3AEC73181396A5CFBF17332CE9B6`.

Astra independently reviewed the tracked patch and the three final evidence
results above for this narrow source/ABI closure. The 10 C probes and two Rust
tests support the helper and its compiler/interpreter wiring; they do not
substitute for the unrun 31-check language fixture or broader producer
qualification.
