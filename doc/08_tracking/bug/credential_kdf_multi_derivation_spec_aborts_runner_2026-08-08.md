# A spec doing several bcrypt KDF derivations aborts the test child with rc=255 and NO verdict

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

- **Filed:** 2026-08-08
- **Severity:** MED (blocks verification, and a landed instance would take down a whole directory run)
- **Area:** test runner child / `std.bcrypt.key_derivation`

## What is wrong

A spec that calls `credential_derive_key` (bcrypt/eksblowfish, then
HKDF-SHA256) **once** runs fine. A spec that calls it roughly ten times kills
the test child: exit code **255**, and — this is the damaging part — **no
`SPEC FILE VERDICT` line at all**.

Because there is no verdict, the failure is invisible to every verdict-based
gate. A grep for `SPEC FILE VERDICT` finds nothing and reads the same as a spec
that was never run.

## Signature

The parent emits ~78,007 bytes of lint/family warnings, prints

```
child binary: /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple
```

and hands off. On the failing runs the log stops at **exactly** 78,007 bytes —
byte-identical across different source revisions, which is what first showed
this was deterministic and not a race. A healthy run continues past that point
with the `✓` lines and grows to ~92 KB.

Not a timeout: `timeout` would give rc 124. Elapsed real time was ~2m37s
against only ~20s of user CPU, so the child was mostly blocked, then died.

## Reproduce

- `test/01_unit/lib/terminal/credential_key_full_width_spec.spl` — 1 derivation
  at cost 4 → `executed=1`, verdict printed. Fine.
- The same file with ~10 derivation-bearing cases → rc=255, no verdict.

`SIMPLE_CREDENTIAL_KDF_COST=4` (the minimum bcrypt cost) is already set in both
cases, so this is not simply cost 10 being slow.

## Consequences

1. A multi-derivation spec **must not be landed**: any lane running
   `bin/simple test test/01_unit/lib/terminal/` would take down the directory
   run with no diagnostic.
2. Derivation-dependent cases have to be split across files, at most two
   derivations each. That is why the credential hardening evidence is split
   between `credential_key_full_width_spec.spl` (1 derivation) and
   `credential_key_file_format_spec.spl` (deliberately bcrypt-free).

## Still unverified because of this

- F2's "two fresh installs give different keys from the same passphrase"
  (2 `credential_key_generate` calls).
- F3's on-disk `stat -c %a` → `600` check (needs 1 `credential_key_generate`).

Both are single- or double-derivation shaped and should be recoverable in
separate files; they were not captured in the session that filed this.

## Fix

Find why the child dies rather than reporting. Two candidates: a per-child
execution-step or allocation limit that bcrypt's ~16k blowfish block
encryptions exhaust, or an unhandled abort in the child that is swallowed
because nothing flushes a verdict on the error path. **Independently of the
root cause, the child must always emit a verdict line** — a silent rc=255 that
greps identically to "not run" is the part that makes this dangerous.

## See also

- `doc/09_report/lib/crypto/credential_store_aes_cbc_adversarial_review_2026-08-08.md`
- `.claude/rules/testing.md` § "Take `$?` from the command under test"
