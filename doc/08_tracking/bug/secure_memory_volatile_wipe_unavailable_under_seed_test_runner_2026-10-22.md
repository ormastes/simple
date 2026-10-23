# std.common.crypto.secure_memory volatile wipe unreachable under the seed test runner

- Bug ID: `secure_memory_volatile_wipe_unavailable_under_seed_test_runner_2026-10-22`.
- Status: observed on the release_phase3 base (`4d058f7c73e`), reproducible with the
  repository-mandated bootstrap-seed binary (`C:/dev/simple/bin/simple.exe`,
  "this Rust-built Simple binary is a bootstrap seed only"). NOT caused by the
  SQLCipher no-padding CBC lane; that lane worked around it locally.
- Owner: runtime/compiler extern surface of the seed binary (out of cipher-a lane
  ownership). The pure-Simple `bin/release/<triple>/simple` may already behave
  differently; this report makes no claim about it.
- Downstream workaround applied: `src/lib/common/aes/modes.spl` zeroizes its own
  scratch with element assignment (`_zeroize_i64`/`_zeroize_u8`) instead of
  calling `secure_zero_*_slots`.

## Observed failure

Every module that transitively calls `secure_zero_u8_slots` /
`secure_zero_u8_range` fails at JIT/semantic stage under
`simple test --no-session-daemon`:

```
semantic: unknown extern function: rt_array_data_ptr_text
```

Pre-existing, lane-independent reproducer at this base (fails identically
without any cipher-a change in the tree):

```
SIMPLE_LIB=$PWD/src bin/simple.exe test --no-session-daemon \
  test/01_unit/lib/database/server/credential_zeroization_spec.spl
# -> 3 passed, 4 failed; every failure is
#    "semantic: unknown extern function: rt_array_data_ptr_text"
```

The symbol itself exists in both runtimes:

- C runtime: `src/runtime/runtime_native.c:8625` (`rt_array_data_ptr_text`).
- Seed symbol table: `src/compiler_rust/common/src/runtime_symbols.rs:143,428`.

So the gap is in the seed's JIT/interpreter extern dispatch table, not in the
declaration or the C side.

## Secondary observation (i64 slot path)

Under the same seed binary the i64-slot wipe *does* link but cannot verify:

```
use std.common.crypto.secure_memory.{secure_zero_i64_slots}
# secure_zero_i64_slots([1,2,3]).verified() == false  (elements then read back
# nonzero / report unverified in interpreter mode)
```

`secure_zero_i64_slots` is therefore also unusable as proof-of-zeroization on
this lane, even where it does not raise the unknown-extern error.

## Impact

- Any library code that wants compiler-resistant scratch wiping via
  `std.common.crypto.secure_memory` is silently untestable through the seed
  test runner: specs either ERROR (u8 path) or assert a wipe that reports
  unverified (i64 path).
- Affected in-tree consumers include the credential-zeroization specs
  (`test/01_unit/lib/database/server/credential_zeroization_spec.spl`,
  `test/fixtures/simpleos_dbd_credential_zeroization/main.spl` and siblings).

## Workaround (in-lane, minimal)

`src/lib/common/aes/modes.spl` (cipher-a ownership) keeps its contract promise
"zeroize scratch where the language allows" with plain element assignment, the
same idiom as `std.common.crypto.x25519_mlkem768.raw_workload_binding`
(`_raw_wipe`): overwrite each slot with `0`/`0u8` before the buffer is dropped.
This leaves no stale bytes in the live buffer but is not compiler-resistant and
performs no readback verification. If this bug is fixed, the
`_zeroize_*` helpers in modes.spl should be re-pointed at
`secure_zero_i64_slots`/`secure_zero_u8_slots`.

## Suggested fix direction (owner lane)

Register `rt_array_data_ptr_text` (and audit the other `rt_volatile_*` /
`rt_memory_barrier` dispatches) in the seed binary's JIT/interpreter extern
table so the semantic pass accepts the same symbol set the C runtime exports;
then re-enable the credential-zeroization specs as regression evidence.
