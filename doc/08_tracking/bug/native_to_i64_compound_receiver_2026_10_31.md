# Native `.to_i64()` returns 0 on a compound or unproven receiver

Status: FIXED IN SOURCE by `8d261cef11b`, native proof pending; the `var t0` row is unexplained. The SQLCipher read path is worked around.
Severity: P0 (silent wrong values). Date: 2026-10-31.

## Symptom

Built by the pinned Phase 2 producer (SHA-256 `13d73267...`), `.to_i64()` returns
0 for every non-zero input on some receivers, with no error:

| Receiver | Result over inputs 0..255 |
| --- | --- |
| `arr.len().to_i64()` | wrong for all 255 non-zero inputs |
| `((w + 1) - 1).to_i64()` | wrong for all 255 non-zero inputs |
| `u8_of(v).to_i64()` | correct |
| typed local `n.to_i64()` | correct |
| `var t0` also assigned from `(x).to_u8()`, then `t0.to_i64()` | returned 0 |

Reproduction: `test/fixtures/devhub/native_codegen_repro/main.spl`, expected red on
the pinned producer. Published vectors guard the crypto:
`test/fixtures/devhub/native_crypto_kat/main.spl` (11/11 pass on Phase 2 after the
workaround). Phase 1 specs pass on these forms.

## Consequences found

- `sqlcipher4_keys.spl`: `passphrase.len().to_i64() == 0` was always true, so every
  key session failed with `SQLCIPHER4_MISSING_SECRET`. This was the Phase 2 cause
  of `devhub_secured_db_key_session_open_failure_2026_10_27.md`.
- `aes_gcm.spl`: the Rcon index was always 0, and `t0` in the AES-256 `m == 4`
  branch was read as 0. The key schedule was wrong but self-consistent, so
  round trips passed while real ciphertext decrypted to garbage. Only known-answer
  vectors expose this class.

## Root cause (2026-10-31)

The compound-receiver rows are the defect in
`native_to_i64_on_binop_receiver_miscompile_2026-10-27.md`, already fixed in source by
`8d261cef11b` (2026-10-27). The pinned producer predates it: its evidence records source
head `fa967a99dcb` (2026-10-25), which does not contain that commit. The tree was dirty, but
its `source-byte-pins.sdn` hashes for `method_calls_literals.spl` and
`builtin_method_extras.spl` equal the blobs at `fa967a99dcb`, so both files are pre-fix.

`rt_to_int_dynamic` is not the source of the 0; it returns a non-text value unchanged.
The path, in `method_calls_literals.spl` on the pre-fix source:

1. The receiver has no HIR type and an I64 MIR local, so `local_is_proven_numeric_scalar`
   (:721) is false and the erased-receiver arm (:2591-2621) admits it as text.
2. `ensure_tagged_str` (:266) emits `rt_interp_cstr`, `rt_string_len`, `rt_string_new`,
   then the arm at :4012 calls `rt_string_to_int_lenient`.
3. In `runtime_native.c`, for a word below 0x10000, `rt_interp_cstr` (:4474) returns NULL
   and `rt_string_len` (:4333) returns -1. `rt_string_new(NULL, -1)` (:4248) returns nil,
   and `rt_string_to_int` (:7468) returns 0 for a non-string.

An input of 0 is correct by accident, which is why 255 of 256 inputs are wrong. A word at
or above 0x10000 is read as a pointer, matching the SEGVs in the 2026-10-27 record.

## Evidence

MIR callees from the real HIR and MIR lowering, run from source in interpreter mode, with
one tree and one binary, toggling only the three `method_calls_literals.spl` changes of
`8d261cef11b`:

| Receiver | Base `0c4ad3785af` | Fix removed |
| --- | --- | --- |
| `.len()` on local, param, text, field, element, call and method results | cast | text parse |
| `((w + 1) - 1)` | cast | text parse |
| typed and untyped `var` reassigned from `.to_u8()` | cast | cast |
| erased `Any`, `text` (controls) | text parse | text parse |

Spec: `test/01_unit/compiler/50.mir/to_i64_compound_receiver_spec.spl`, 12 of 12 on the
base. It is green because source is already fixed; no compiler code changed.
Run it with `SIMPLE_EXECUTION_MODE=interpret`, using `run`: on the deployed Rust seed,
`test` exited 0 with no results, and the JIT panicked in `cranelift-jit` `compiled_blob.rs:58`.

## Still open

- No compiler built from the fixed source has been checked in this investigation, so
  `test/fixtures/devhub/native_codegen_repro/main.spl` is not yet proven green. Close this
  record only after it passes on a rebuilt compiler.
- The `var t0` row is NOT explained. The AES shape lowers to a cast on the base and with
  the fix removed, so `8d261cef11b` alone does not account for it. The probes were
  single-module and used the same `-> u8` helper signatures as `aes_gcm.spl`. The probes did
  not run on the producer's own tree, and other commits since `fa967a99dcb` were not toggled.
  Keep the `aes_gcm.spl` workaround until the known-answer vectors pass without it on a
  rebuilt compiler.

## Remaining exposure

The form `.len().to_i64()` appears in 504 places across 129 files under `src/lib`,
`src/app` and `src/compiler`. Only the SQLCipher read path was changed. Those sites need
no edits. They are wrong only in binaries built by a producer without the fix.
