# JIT/HIR: `Some(x)` binding double-unwraps when the optional's payload is itself an enum

**Date:** 2026-08-24
**Severity:** HIGH (silent wrong value, no crash)
**Status:** FIXED in the seed source. **NOT deployed** — reaching `bin/simple` needs a seed rebuild+redeploy owned by the bootstrap lane.
**Fix:** `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs`

## Defect

Binding `case Some(x)` has to cope with two representations of `T?`: a boxed
`Option` enum (literal `Some(v)`) and the "raw migration form" (the bare
payload, which natively compiled `T?`-returning functions produce). The lowering
discriminated them at runtime with

```text
if rt_enum_id(subj) >= 0: rt_enum_payload(subj)   # assume boxed Some
else:                     subj                    # raw payload
```

`>= 0` only asks *"is the subject some enum"*. That is ambiguous exactly when
the payload type is **itself an enum**: a raw `SdnValue?` holding
`SdnValue.Dict(d)` IS a real enum, so the test took the boxed branch and asked
`rt_enum_payload` for the SdnValue's OWN payload — unwrapping one level too far
and binding `d` instead of the `SdnValue`. Nothing crashes; the binding is
simply the wrong value, so every later read answers as if the data were absent.

The runtime already had the correct rule and the identical reasoning, in
`rt_unwrap_or_self` (`runtime/src/value/objects.rs:318`): *"Only the canonical
Option enum uses this compatibility helper. User enums may also be boxed
RuntimeEnum values; unwrapping those would turn `K? ?? fallback` into K's
payload and corrupt a later match."* The match lowering just never agreed with
it.

## Fix

One comparison: `rt_enum_id(subj) >= 0` → `rt_enum_id(subj) == OPTION_ENUM_ID`
(the reserved id `1`, mirrored from `runtime/src/value/objects.rs:259` with a
comment tying the two together). A user enum never has that id.

## Evidence

Minimal repro, self-contained apart from `SdnValue` (an enum), driving both
representations of the same optional:

```console
$ bin/simple run ax2.spl        # stock seed, JIT, 0 jit-fallbacks
RAW inline-arm kind=other       # <-- wrong: bound the payload, not the SdnValue
BOXED inline-arm kind=Dict
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run ax2.spl
RAW inline-arm kind=Dict        # interpreter is correct
BOXED inline-arm kind=Dict
$ /mnt/data/cargo-target-jitfix/release/simple run ax2.spl   # rebuilt seed
RAW inline-arm kind=Dict        # <-- fixed
BOXED inline-arm kind=Dict
```

`SIMPLE_JIT_STRICT=1` reproduces too, and `grep -c 'jit-fallback|falling back'`
is 0 on every run, so the JIT genuinely executed rather than silently deopting.

**Seed test suite** (same target dir, both builds from identical origin content
apart from this diff): `FAILED. 3866 passed; 8 failed` **before and after, with
a byte-identical failure list**. No regression, and no repair.

A correction worth recording, because it nearly became a false claim: an earlier
measurement appeared to show this fix repairing
`test_if_let_identifier_binding_copies_subject_value` and
`test_if_val_exists_check_binds_unwrapped_option_value` — two tests named for
exactly this defect class. That was an artifact of a stale working copy (98
lines behind origin), not of the change. Re-measured with the fix re-applied to
clean origin content, both tests are red before AND after; they are a separate
pre-existing failure (`control_flow_tests.rs:612`) that this fix does not
address. The A/B above is the only claim supported by evidence.

## Scope: what this does NOT explain

A second, distinct defect with a similar surface is still OPEN. Reading through
a `case Some(x)` binding taken from a **parser-built** `SdnValue` tree still
answers as if keys were absent, and this fix does not change that:

- hand-built `SdnValue` + inline arm -> correct, before and after;
- `parse()`-built `SdnValue` + inline arm -> wrong, before and after;
- hoisting into a `var` first -> correct in both.

That is the defect worked around in `package_pins.spl` and
`completeness_seal/manifest.spl` (commit `6d35617d429`). Those hoists remain
necessary. Root cause unknown; the parser-built tree is not itself corrupt,
because the hoisted read finds every key.

## Deployment

The fix is in the Rust seed, so it changes nothing for anyone until a seed
rebuild is deployed to `bin/simple`. That is the bootstrap lane's redeploy, and
this record must not be read as "deployed". Verified only against a locally
built binary at `/mnt/data/cargo-target-jitfix/release/simple`
(60359136 bytes, 2026-08-24 21:38 UTC); the shared `bin/simple` was deliberately
NOT replaced, since other lanes' runs are bracketed against it.
