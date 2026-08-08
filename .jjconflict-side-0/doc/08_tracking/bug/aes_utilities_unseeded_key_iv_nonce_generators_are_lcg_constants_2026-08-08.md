# AES utilities: `generate_aes_key` / `generate_iv` / `generate_nonce` are constant-seeded LCGs

- **Date:** 2026-08-08
- **Status:** OPEN — filed, not fixed (file is contested; see "Why filed, not fixed")
- **Severity:** Medium *as currently wired* (zero callers), High as a latent trap
- **Component:** `src/lib/common/aes/utilities.spl`
- **Related:** `doc/08_tracking/bug/credential_store_aes_cbc_label_is_actually_ctr_with_deterministic_iv_2026-08-06.md`
  (the sibling defect in the same file that triggered this family sweep)

## Summary

Three generators in `src/lib/common/aes/utilities.spl` that the API names present
as random-key/IV/nonce sources are constant-seeded glibc-style LCGs. Each returns
**the same bytes on every call, in every process, forever**.

| Function | Line | Seed | Behaviour |
|---|---|---|---|
| `generate_aes_key(size)` | 233-252 | constant `42` | Every AES key ever produced is byte-for-byte identical |
| `generate_iv()` | 255-267 | constant `123` | Every IV is byte-for-byte identical |
| `generate_nonce()` | 270-271 | — | Alias for `generate_iv()`; inherits the defect verbatim |

All three use `seed = (seed * 1103515245 + 12345) % 2147483648`, taking `seed % 256`
per byte. There is no entropy input of any kind.

`generate_iv_from_seed` (line 274-285) is the same LCG and is covered by the
separate bug doc listed under "Related" — it is *not* re-filed here.

## Real exploitability

**Currently unexploitable: these three have zero callers.** A sweep of
`src/**`, `test/**` and `examples/**` for `generate_aes_key`, `generate_iv` and
`generate_nonce` — matching the bare call, the qualified `module.fn` form, and
`use std.common.aes.utilities.{...}` import lists — found **no call site outside
`utilities.spl` itself**. The only externally-imported symbol from this module is
`generate_iv_from_seed`, via `src/lib/nogc_sync_mut/terminal/credential/store.spl:16`.

So the correct severity today is **dangerous dead API**, not an active break. The
reason it is still worth filing rather than shrugging off:

- The names (`generate_aes_key`, `generate_iv`, `generate_nonce`) are exactly what
  a caller reaches for when wiring new AES code, and nothing at the call site would
  reveal the constant. The in-file comments admit the weakness, but comments are
  not visible at the import site.
- The identical helper in this same file (`generate_iv_from_seed`) *did* get wired
  into the credential store, which is the defect that started this sweep. The
  failure mode is demonstrated, not hypothetical.
- A constant AES key plus a constant IV is a total loss of confidentiality —
  identical plaintexts produce identical ciphertexts, and the key is a compile-time
  constant recoverable by anyone with the source.

## Recommended fix

Replace all three bodies with OS-CSPRNG draws, using the pattern proven in this
sweep and already used correctly by
`src/lib/gc_async_mut/gpu/browser_engine/net/ws_crypto.spl:9`:

```
extern fn rt_random_i64() -> i64
```

`rt_random_i64` is backed by `rand::rngs::OsRng` on the Rust interpreter path
(panics rather than degrading on entropy failure) and by a `/dev/urandom` read in
`src/runtime/runtime.c:2016-2036`. Landed examples of this exact fix:
`src/lib/common/bcrypt/salt.spl` and
`src/lib/nogc_sync_mut/tls/_TlsUtilities/hex_encoding.spl`.

Alternatively — and preferably, given zero callers — **delete all three**. Dead
crypto API that is wrong is worse than no API.

## Why filed, not fixed

`src/lib/common/aes/utilities.spl` is being actively edited by a concurrent lane
repairing `generate_iv_from_seed` and its credential-store call site. Editing the
same file concurrently risks clobbering that lane's work. The three generators
here are not reachable, so there is no urgency that justifies the collision risk.

## Verification note for whoever fixes this

Stdlib `.spl` edits are **not** live under `bin/simple run` — that path resolves
`std.*`/`lib.*` to a bundled stdlib and silently ignores on-disk edits (a
sabotage-to-constant had zero effect). They **are** live under `bin/simple test`.
Verify through a spec run, not a script run. See
`doc/08_tracking/bug/stdlib_spl_edits_not_live_under_bin_simple_run_2026-08-08.md`.

Test shape: salt/key/IV generation has no published vectors. Assert (a) two
successive calls differ, (b) length and byte range are correct, and (c) the output
is not the old LCG's exact stream. Pattern:
`test/07_security/csprng_salt_iv_spec.spl`.
