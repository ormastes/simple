# Bug: Digest.hex() returns garbage when seam.spl and ctypes are both imported

## Closed 2026-09-13 — Does not reproduce: `Digest.hex()` is correct under the double import

- **measured** (Rust seed `bin/simple` v1.0.0-rc.1, Windows): a file importing BOTH `std.common.crypto.typed.seam` and `std.common.crypto.typed.ctypes.{Digest}` — the exact double-import shape — then calling `Digest.new([0u8, 1u8, 2u8, 255u8]).hex()` prints `hex=000102ff len=4`. That is the payload bytes, correctly hex-encoded, not the struct representation bytes.
- **measured**: `len()` agrees at 4, so the previously-unaffected accessors are still fine and `hex()` has joined them.
- **inferred**: the original driver was `SIMPLE_BOOTSTRAP_DRIVER=bin/release/x86_64-unknown-linux-gnu/simple_seed`, a Linux artifact absent here; the Windows seed was used instead, so this is "does not reproduce on the current seed" rather than a located fix.

**ID:** digest_hex_double_import_corruption_2026-06-15
**Filed:** 2026-06-15
**Status:** CLOSED 2026-09-13 (does not reproduce). **Severity:** P1 — silent data corruption; hex() returns structurally plausible but wrong hex strings
**Component:** interpreter — cross-module struct method dispatch when two modules both import ctypes
**Driver:** `SIMPLE_BOOTSTRAP_DRIVER=bin/release/x86_64-unknown-linux-gnu/simple_seed`

## Summary

When `seam.spl` (which imports `std.common.crypto.typed.ctypes.{Digest}`) and the
caller's file both import `ctypes`, calling `Digest.new(data).hex()` in the caller
returns garbage — a hex-encoded string of the **struct representation bytes** rather
than the payload bytes.

`Digest.len()` and `Digest.ct_eq()` are unaffected; only `hex()` is corrupted.
The bug triggers in `fn main()` context, not only in `describe/it` blocks.

## Minimal repro

```simple
# File A: src/lib/common/crypto/typed/seam.spl
use std.common.crypto.typed.ctypes.{Digest}
# ... any fn that uses Digest ...

# File B (the spec or main file):
use std.common.crypto.typed.seam.{alpha_run_digest}
use std.common.crypto.typed.ctypes.{Digest}

fn main():
    val data: [u8] = [1u8, 2u8, 3u8]
    val d = Digest.new(data)
    print(d.hex())   # CORRUPTED: prints garbage like "484948504851" instead of "010203"
    print(d.len().to_text())   # CORRECT: prints 3
    print(d.ct_eq(Digest.new(data)).to_text())   # CORRECT: prints true
```

Run:
```bash
export SIMPLE_BOOTSTRAP_DRIVER=bin/release/x86_64-unknown-linux-gnu/simple_seed
bin/simple run <above_file>
```

## Observed

```
484948504851   # garbage hex, appears to be hex-of-ASCII-of-hex representation bytes
3              # correct
true           # correct
```

## Expected

```
010203         # correct hex encoding of [1, 2, 3]
3
true
```

## Conditions required to reproduce

1. Module A imports `ctypes.{Digest}` and exports any function that uses Digest
2. Module B (caller) imports BOTH Module A AND `ctypes.{Digest}` directly
3. Caller calls `Digest.new(data).hex()`
4. Interpreter mode (not confirmed in AOT/native)

The key trigger is the **double import** — if Module A does not also import ctypes,
the corruption does not occur.

## Distinction from related bugs

- `cross_module_struct_method_poisons_itblock_byte_ops_2026-06-15.md`: that bug
  affects byte ops in `it` blocks specifically; this bug triggers in `fn main()`
  and is specific to `hex()` (not all byte ops).
- The cited bug claims "a plain `fn main()` is fully correct" — this repro
  contradicts that claim for the double-import case, suggesting a distinct root cause
  or a more general version of the same defect.

## Impact

Any code that imports a module that uses Digest AND also directly imports Digest
cannot rely on `.hex()` output. Only `ct_eq()`, `len()`, and `.bytes()` (→ ByteSpan,
then `.get()`) are safe cross-module.

## Workaround

Use `ct_eq(Digest.new(known_bytes))` for equality checks instead of comparing
`.hex()` strings. For display/debugging, access bytes via `.bytes().get(i)` in a loop.

## Related

- `doc/08_tracking/bug/cross_module_struct_method_poisons_itblock_byte_ops_2026-06-15.md`
- `doc/08_tracking/bug/dual_backend_generic_typed_seam_2026-06-15.md`
