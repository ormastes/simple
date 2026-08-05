# `rt_tls13_sha256` returns an EMPTY digest under the Cranelift JIT — silently

**Status:** OPEN
**Found:** 2026-08-05
**Severity:** HIGH — silent wrong-answer in a crypto digest channel, exit 0
**Component:** `rt_tls13_sha256` runtime binding under the Cranelift JIT;
surfaces through `src/lib/common/crypto/sha256.spl:197` (`sha256_text`)

## Symptom

Under `SIMPLE_EXECUTION_MODE=jit`, `sha256_text(...)` returns `""` for **every**
input. No error, no diagnostic, no panic, exit code 0.

This matters because **`bin/simple run` defaults to the JIT**. Any program that
hashes via `sha256_text` and is run the ordinary way gets an empty digest and no
indication anything went wrong.

## Isolation — which extern, not inferred

`sha256_text` calls two externs. Splitting them
(`src/app/test/x25519mlkem768_sha256_extern_probe.spl`) names the culprit
exactly:

| call | `interpret` | `jit` |
|---|---|---|
| `rt_text_to_bytes("abc")` | len 3 | len 3 — **fine** |
| `rt_tls13_sha256(bytes)` | **len 32**, first byte 186 (`0xba`) | **len 0** |

`rt_text_to_bytes` is healthy under both engines, so this is not a general
`[u8]`-return-across-the-extern-boundary failure. It is `rt_tls13_sha256`
specifically. Interpreter first byte `0xba` is correct — SHA-256("abc") is
`ba7816bf…`.

## Size sweep — not an edge case

`src/app/test/x25519mlkem768_sha256_identity_probe.spl`, run under each engine:

| n | bytes | interpret digest len | jit digest len |
|---|---|---|---|
| 0 | 0 | 64 | 0 |
| 1 | 29 | 64 | 0 |
| 2 | 58 | 64 | 0 |
| 7 | 203 | 64 | 0 |
| 30 | 890 | 64 | 0 |
| 64 | 1,910 | 64 | 0 |
| 129 | 3,889 | 64 | 0 |
| 1025 | 31,690 | 64 | 0 |

Empty at every size including n=0. Interpreter digests are correct against the
published FIPS 180-4 vector: n=0 →
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

## Reproduce

```bash
SIMPLE_EXECUTION_MODE=interpret bin/simple run \
    src/app/test/x25519mlkem768_sha256_extern_probe.spl   # tls13_sha256 len=32
SIMPLE_EXECUTION_MODE=jit       bin/simple run \
    src/app/test/x25519mlkem768_sha256_extern_probe.spl   # tls13_sha256 len=0
```

Score the `PROBE tls13_sha256 len=` line, **not** the exit code or the verdict
line — both probes print `PROBE VERDICT: PASS` and exit 0 even when the digest
is empty. That is the whole hazard.

## Why this is worse than a slow path

It manufactures false green. A caller that hashes, compares two digests, and
asserts equality gets `"" == ""` → true. Any "digests are byte-identical across
engines" check written the obvious way passes *because* both sides are empty.

This already caused a wrong published conclusion: the qualified-timing campaign
recorded "`sha256_text` under the JIT is 4.0x faster with an identical digest"
and prescribed moving measurement onto a JIT driver. The JIT was not faster at
hashing — it was not hashing. Had that route been taken the campaign would have
pinned receipts derived from empty digests. See
`doc/08_tracking/bug/qualified_timing_blocked_by_interpreted_sha256_2026-08-05.md`
§ "The JIT arm was never 4x faster".

## Blast radius beyond this campaign

`src/lib/common/crypto/sha256.spl:176-182` names `rt_tls13_sha256` as "the
established digest channel for std TLS/SSH", pointing at
`src/lib/nogc_async_mut_noalloc/tls/{client,transcript}.spl` and
`src/os/apps/sshd/ssh_session_kex.spl`. Those paths are owned by other lanes and
were **not** inspected here — whether they reach the JIT in practice is
unverified and should be checked before this is triaged as campaign-local.

## Suggested next step

Check whether `rt_tls13_sha256` is registered in the JIT's extern table at all;
an unregistered `@extern fn` returning silent-nil under the JIT only is a known
shape in this codebase. If so, the fix is registration plus a guard that makes
an unregistered extern fail loudly rather than return an empty aggregate.

A regression guard belongs in the `engine_probe` form
(`src/lib/nogc_sync_mut/spec/engine_probe.spl`), asserting the probe's
`tls13_sha256 len=32` line under **both** named engines — a spec body can never
reach the JIT itself, so an in-process `expect` cannot catch this.
