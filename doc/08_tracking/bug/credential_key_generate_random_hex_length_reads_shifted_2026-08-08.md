# Fresh installs could never create a credential key — `.length()` on the `??`-unwrapped `rt_random_hex` result reads chars>>3

- **Filed:** 2026-08-08
- **Severity:** CRITICAL (key generation impossible; encryption always failed closed)
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
  (local workaround); the underlying compiler defects stay OPEN
- **Area:** compiler (seed JIT) / `src/lib/nogc_sync_mut/terminal/credential/store.spl`

## What was wrong

`credential_key_generate` draws its per-install KDF salt like this:

```
val salt_hex_opt = rt_random_hex(KDF_SALT_SIZE)
if salt_hex_opt == nil:
    return false
val salt_hex = salt_hex_opt ?? ""
if salt_hex.length() != (KDF_SALT_SIZE * 2):
    return false
```

`rt_random_hex` returns the **correct** 32-character hex text — the value is
right, and printing it shows all 32 characters. But `.length()` on the value
that comes straight out of the `??` unwrap reads the character count
**shifted right by 3**. The guard therefore always fired and the function
returned `false` before deriving or writing anything. No key file was ever
created on a fresh install, so `credential_encrypt` (which needs a key) always
returned `""`.

`credential_encrypt` had the identical shape for its per-record IV
(`val iv_hex = iv_hex_opt ?? ""` then `iv_hex.length() != 32`), so that path
was dead for the same reason.

## Measured (JIT, `bin/simple run`, 2026-08-08)

```
RH_VALUE=cf58ed7d7b8327b1e3e6a1ae55490836      # 32 chars, correct
RH_LEN=4                                       # 32 >> 3
RH_TRIM_LEN=32                                 # .trim() first -> correct
RH_INTERP_LEN=32                               # interpolation round-trip -> correct
```

8 characters read as 1, 32 as 4 — a right-shift by 3, the mirror of the
left-shift-3 in the `list`-param family. Not a `??` artifact in the sense of a
wrong value: the unwrapped and non-unwrapped values agree and are correct; only
`.length()` on that binding is wrong.

## Why the guard could NOT simply be deleted

`hex_to_bytes` loops on `hex.length()`. Dropping the `!= 32` check does not get
you a valid salt — it gets you a silently **2-byte** salt, which is strictly
worse than failing closed. The fix has to repair the length read.

## Second defect found while fixing it — nested string literal inside an interpolation

The obvious one-liner does **not** work:

```
val salt_hex = "{salt_hex_opt ?? \"\"}"      # WRONG
```

Measured: this produces the 6-character literal text `{o ?? ` — the
interpolation is terminated at the inner `"` and the remainder is emitted
verbatim, with **no diagnostic**. Silent corruption.

```
RAW_LEN=4  INLINE_INTERP_LEN=6  TWOSTEP_LEN=32
RAW_VAL=b2c2086874af29b836b22e248458109e
INLINE_VAL={o ??
TWOSTEP_VAL=b2c2086874af29b836b22e248458109e
```

This is a **separate, unfiled parser defect**: a string literal nested inside
an `{...}` interpolation is mis-lexed and the mis-parse is silent. Recorded
here because it directly shaped the fix; it warrants its own compiler bug.

## The fix

Two steps, and the second must be on its own line:

```
val salt_hex_raw = salt_hex_opt ?? ""
val salt_hex = "{salt_hex_raw}"
```

Same shape applied to `iv_hex` in `credential_encrypt`. The guards are kept.

## Positive control

- Pre-fix: `salt_hex.length()` = 4, `GEN=false`, **no file created**.
- Post-fix (replicating the exact sequence against the live stdlib):
  `S3_LEN=32`, `S3_GUARD_PASSES=true`, `S3_SALT_BYTES=16`, `KEY_LEN=32`,
  key file written well-formed at 100 chars, `credential_encrypt` /
  `credential_decrypt` round-trip `true`.
- Edit-visibility proven first by a `SABOTAGE_MARKER_7731` return injected into
  `bytes_to_hex` and observed in the probe output — `bin/simple run` from a
  directory without `src/lib/` silently serves a bundled stdlib.
- The interpreter is correct on all of this, so `bin/simple test` cannot see it.

## Related

- `doc/08_tracking/bug/jit_param_passed_list_element_read_returns_tagged_2026-08-08.md` (sibling shift defect, OPEN)
- `doc/08_tracking/bug/credential_store_key_and_salt_corrupted_by_list_param_hex_2026-08-08.md`
- `doc/08_tracking/bug/rt_package_chmod_family_fails_from_jit_key_left_world_readable_2026-08-08.md`
