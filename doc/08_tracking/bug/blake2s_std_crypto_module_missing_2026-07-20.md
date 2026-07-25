# `std.crypto.blake2s` module does not exist (only `os.crypto.blake2s`)

- **Date:** 2026-07-20
- **Area:** `src/lib/common/crypto/` (missing file)
- **Severity:** medium (whole spec file cannot load; 0 examples run).
- **Status:** OPEN.

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/blake2s_spec.spl --no-session-daemon
```

```
error: runtime: Module "std.crypto" does not export 'blake2s'
error: test-runner: no examples executed
```

## Root-cause hypothesis

`test/unit/lib/crypto/blake2s_spec.spl:26` imports
`use std.crypto.blake2s.{blake2s_hash, blake2s_init, blake2s_update, blake2s_final}`.
The spec's own header comment (line 4) states the implementation lives at
`src/lib/common/crypto/blake2s.spl` — but that file does not exist
(`ls src/lib/common/crypto/blake2s.spl` → No such file or directory). The
only implementation in the tree is `src/os/crypto/blake2s.spl`
(`os.crypto.blake2s`, a parallel/no_std-oriented namespace also used by
other crypto modules in this codebase, e.g. `poly1305.spl` is duplicated
under both `lib/common/crypto/` and `os/crypto/`).

This was **not** fixed as a simple import-path swap
(`std.crypto.blake2s` → `os.crypto.blake2s`) because:
1. It is unverified whether `os.crypto.blake2s`'s function signatures and
   byte-exact output match what this spec (cross-verified against Python
   `hashlib.blake2s`) expects — swapping the import without checking risks
   silently masking a real behavioral difference between the two mirrors.
2. There are three pre-existing `blake2s_spec.spl` files in the tree
   (`test/unit/lib/crypto/`, `test/01_unit/lib/crypto/`,
   `test/01_unit/lib/crypto/.spipe_matchers_blake2s_spec.spl`) and this
   cluster's scope is `test/unit/lib/crypto/` only — a path fix here should
   be made by someone who can also confirm/port the `std.crypto.blake2s`
   surface for the other consumers of that namespace.

## What NOT to do

Do not blindly repoint the import at `os.crypto.blake2s` without verifying
byte-exact parity with the Python-cross-checked KAT values in this spec.

## Affected specs

- `test/unit/lib/crypto/blake2s_spec.spl` (0 examples executed — load
  failure)
