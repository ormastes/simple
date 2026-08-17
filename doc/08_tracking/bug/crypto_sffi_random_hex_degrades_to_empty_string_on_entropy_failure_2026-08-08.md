# `crypto_sffi.random_hex` degrades to an empty string on CSPRNG failure, and `random_salt()` inherits it

- **Date:** 2026-08-08
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Severity:** Medium (fail-open on a rare path, but the failure is silent and lands in a salt)
- **Component:** `src/lib/nogc_sync_mut/io/crypto_sffi.spl`

## Summary

`rt_random_hex` is declared nullable and returns nil when the OS entropy provider
fails. The Simple wrapper swallows that failure with `?? ""`:

```
# src/lib/nogc_sync_mut/io/crypto_sffi.spl:49-50
extern fn rt_random_bytes(length: i64) -> text
extern fn rt_random_hex(length: i64) -> text?

# line 317
fn random_hex(length: i64) -> text:
    rt_random_hex(length) ?? ""
```

`random_salt()` (line 332) is a thin wrapper over it:

```
fn random_salt() -> text:
    """Generate random salt for password hashing (16 bytes, hex)
    Returns: 32-character hex string
    """
    random_hex(16)
```

So on entropy failure, `random_salt()` returns `""` — not an error, not a
32-character hex string, just an empty salt — while its doc-comment still promises
"32-character hex string". Callers that use the result as a password-hashing salt
get an empty, constant salt for every password, silently.

The distinction from the LCG family swept alongside this: those generators were
*always* weak. This one is correct on the happy path and fails open only when the
CSPRNG is unavailable. That is rarer, but it is also the case nobody tests.

## Real exploitability

Bounded, and honestly on the low side of "medium":

- `rand::rngs::OsRng` failing is genuinely rare on a healthy Linux host. The
  realistic triggers are early boot before the entropy pool is initialised,
  a container or chroot without `/dev/urandom`, or fd exhaustion.
- The blast radius when it does trigger is bad and undetectable: every password
  hashed during that window shares an empty salt, defeating the salt's entire
  purpose (rainbow-table and cross-user-comparison resistance), with no error
  surfaced to any caller or log.

The same file already contains the seam for doing this properly —
`secure_entropy_hex_valid` (line 319) validates that a value is exactly 32
lowercase hex characters and not all zeros. It is described as a "test seam for
the future private command-capability entropy owner" and is **not** currently
applied to `random_hex`'s output. The check exists; it just is not wired to the
path that needs it.

## Recommended fix

Do not paper over a CSPRNG failure. Either:

1. **Fail closed.** Change `random_hex` / `random_salt` to return
   `Result<text, text>` and propagate the failure, so callers must handle it. This
   is the correct fix but changes the signature and touches every call site.
2. **Fail loudly at minimum.** Keep the signature and make entropy failure a hard
   abort rather than an empty string. An unavailable CSPRNG is not a recoverable
   condition for a salt.

Option 1 is preferred. In either case, wire `secure_entropy_hex_valid` in as a
post-condition on the returned value so a short, non-hex, or all-zero result is
rejected rather than returned.

Whichever is chosen, the `?? ""` must go — that operator is what converts a
detected failure back into a silent one.

## Verification note

Stdlib `.spl` edits are **not** live under `bin/simple run` (that path resolves to
a bundled stdlib and ignores on-disk edits). They **are** live under
`bin/simple test`. See
`doc/08_tracking/bug/stdlib_spl_edits_not_live_under_bin_simple_run_2026-08-08.md`.

Testing the failure path needs the provider stubbed to return nil;
`random_hex_provider_failure_returns_nil_parity` in
`src/compiler_rust/compiler/src/interpreter_extern/random.rs` is the existing
Rust-side test of that behaviour and shows how the nil is produced.

## Re-verification 2026-08-17 (stdlib slice G, content-classified)

**ALREADY-FIXED (verdict by CONTENT).** `src/lib/nogc_sync_mut/io/crypto_sffi.spl`
no longer contains `rt_random_hex(length) ?? ""`. Line 366 now reads
`checked_entropy_hex(rt_random_hex(length), length)`, and the docstring at :357
states "FAILS CLOSED. This used to be `rt_random_hex(length) ?? ""`, which turned a
..." — i.e. the fail-open degradation is gone and the doc block records it.
Closing.
