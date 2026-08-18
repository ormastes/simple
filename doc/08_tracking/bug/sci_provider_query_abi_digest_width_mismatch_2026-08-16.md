# SCI/provider-query ABI digest width mismatch blocks exact admission

Date: 2026-08-16
Status: PARTIALLY FIXED (2026-08-17) — the width mismatch itself is GONE:
a lossless 256-bit digest now crosses the ABI and the host compares all 256
bits before invoking (unblock conditions 1-3 and the four fixture classes of
condition 4 are done, with executed evidence below). **Exact ABI admission is
still NOT fully signed off**: condition 4's *"one admitted native execution"*
was NOT performed — no provider `.so`/`.smf` was built and loaded in this pass.
Per this record's own rule, no native/SMF provider PASS may be claimed yet.

## Impact

SCI interface groups lock `abi_digest` as one canonical lowercase 64-hex
SHA-256 string, while `SimpleProviderQueryResultV1.abi_digest` is one `u64`.
`app.simple_core.provider_dispatch` can validate that the SCI value is shaped
correctly, but it cannot compare the two identities without an invented,
collision-prone truncation rule. Dynamic activation therefore lacks exact ABI
identity binding even though artifact bytes, query stability, descriptor size,
and major/minor compatibility are checked.

Affected source:

- `src/lib/nogc_sync_mut/composition/types.spl` (`SimpleInterfaceGroupRecordV1`)
- `src/lib/nogc_sync_mut/composition/provider_contract.spl`
  (`SimpleProviderQueryResultV1`)
- `src/app/simple_core/provider_dispatch.spl`

## Required decision

Freeze one lossless wire representation shared by SCI and provider query. The
preferred v2-compatible direction is four ordered `u64` SHA-256 words (or one
fixed 32-byte arena field) with explicit byte order. Do not truncate or hash a
hash into `u64`, and do not compare display text across the ABI.

## Unblock condition

1. Version the query-result prefix without changing existing v1 offsets.
2. Encode/decode the complete digest deterministically in provider and host.
3. Compare the locked SCI ABI digest before publishing a live pin.
4. Add malformed, mismatch, compatible-prefix, and exact-match fixtures plus
   one admitted native execution. Until then, exact ABI admission is blocked
   and no native/SMF provider PASS may be claimed.

## Resolution (2026-08-17)

The frozen wire representation is **four ordered `u64` SHA-256 words**, `w0`
first, each word big-endian (`w0` = digest bytes 0..7, `w1` = 8..15, `w2` =
16..23, `w3` = 24..31). Big-endian was chosen so the word tuple reads in the
same order as the hex text. Nothing is truncated, nothing is re-hashed, and
display text is never compared across the ABI.

Versioning without moving a V1 field: `SIMPLE_PROVIDER_QUERY_RESULT_V2_SIZE`
is 92 = the unchanged 60-byte V1 record plus the 32 digest bytes at offsets
60..91. The host now allocates and **zeroes the full 92 bytes** before the
call, so a V1-only provider that writes 60 bytes yields an all-zero tail, which
decodes as *"no digest declared"* and is REJECTED — never treated as a match,
and never read as stale heap.

Changed files:

- `src/lib/nogc_sync_mut/composition/provider_contract.spl` — `SimpleAbiDigest256V1`,
  `SimpleProviderQueryResultV2`, `SIMPLE_PROVIDER_QUERY_RESULT_V2_SIZE`.
- `src/lib/nogc_sync_mut/composition/abi_digest.spl` (new) — the ONLY hex<->words
  converter; rejects wrong length, uppercase/non-hex, and the all-zero sentinel.
- `src/os/smf/provider_query_wire.spl` — `encode/decode_provider_query_result_v2`;
  the V1 prefix is written by the V1 encoder unchanged, so the two versions
  cannot drift.
- `src/os/posix/dynlib_sffi.spl` — 92-byte zeroed result buffer, V2 decode,
  `ProviderQueryCallV1.abi_digest_256`.
- `src/os/smf/provider_loader.spl` — error-path constructor carries a zero digest.
- `src/app/simple_core/provider_dispatch.spl` — `simple_core_provider_abi_digest_verdict_v1`
  compares the locked SCI hex against the provider's 256 bits and, on any
  disagreement, releases the pin, closes the session, and returns the new
  `SIMPLE_CORE_PROVIDER_DISPATCH_ABI_DIGEST_MISMATCH` (7) WITHOUT invoking.
- `src/app/provider_cli/native_provider_v1.spl` — emits the V2 result with a
  frozen digest (`f173c682…41db`, SHA-256 of the canonical ABI descriptor text).
  The legacy `abi_digest: u64` field stays at its V1 offset for wire
  compatibility only and is no longer the ABI identity.
- `test/01_unit/app/simple_core/provider_abi_digest_admission_spec.spl` (new fixtures).

### Evidence

```
$ readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
59537240 2026-08-17 12:58:51.339525019 +0000
```

`bin/simple --version` prints the bootstrap-seed banner, so this is DIAGNOSTIC
evidence, not release evidence. No file under `src/runtime/*.c` was touched, so
`check-c-runtime-compiles-push.shs` was not applicable to this change.

**`bin/simple test` could not be used and is NOT quoted as a pass.** On this
binary the new spec, `test/01_unit/os/smf/provider_query_wire_spec.spl` and
`test/01_unit/app/simple_core/provider_dispatch_spec.spl` each printed only
warning lines (the new spec: 1222 lines on one run and 2483 on a rerun; the two
existing specs: 19 lines each) with **no `Results:` line** and exited 0 —
the silent-green mode recorded in `.claude/rules/testing.md` and
`doc/08_tracking/bug/test_runner_emits_no_result_summary_silent_exit0_2026-08-17.md`.

The identical assertions were therefore executed directly, via a scratch driver
that calls the same public functions (`<scratch>/abi_check.spl`):

```
$ bin/simple run <scratch>/abi_check.spl
PASS codec.roundtrip = f173c682babeca323ed37f1d64e99ae09694ef2a16934c45d57b3c6bfba541db
PASS codec.short = abi-digest-length-invalid
PASS codec.uppercase = abi-digest-not-lowercase-hex
PASS codec.allzero = abi-digest-all-zero
PASS prefix.w0-collides = yes
PASS prefix.full-differs = differ
PASS wire.encode-ok = ok
PASS wire.size = 92
PASS wire.tail-32 = 32
PASS wire.decode-ok = ok
PASS wire.v1-field-preserved = 1129072945
PASS wire.digest-lossless = f173c682babeca323ed37f1d64e99ae09694ef2a16934c45d57b3c6bfba541db
PASS wire.v1-provider-decodes = ok
PASS wire.v1-provider-handle = 1129072945
PASS wire.v1-provider-no-digest = 0
PASS admit.exact =
PASS admit.prefix-collision-rejected = provider-abi-digest-mismatch
PASS admit.different-rejected = provider-abi-digest-mismatch
PASS admit.undeclared-rejected = provider-abi-digest-not-declared
PASS admit.malformed-lock-rejected = provider-abi-digest-locked-invalid:abi-digest-length-invalid
PASS dispatch.invalid-activation = 1
PASS dispatch.absent-artifact = 2
SUMMARY failures=0
```
(exit code 0, taken from the command itself, not through a pipe.)

`prefix.w0-collides = yes` together with `prefix.full-differs = differ` is the
load-bearing one: the two digests share their entire first `u64`, so the old
truncate-to-`u64` rule would have called them EQUAL, and the new comparison
rejects them.

### Remaining blocker

Unblock condition 4 is only partly met. The four fixture classes exist and pass;
**the "one admitted native execution" does not** — building a provider artifact,
loading it through `provider_admit_dynamic_v1`, and observing a real
`rt_provider_query_v1_call` return the 92-byte V2 record was not done in this
pass. Until that runs, exact ABI admission stays unsigned-off and no native/SMF
provider PASS may be claimed.
