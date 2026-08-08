# `rt_tls13_sha256` returns an EMPTY digest under the Cranelift JIT — silently

**Status:** FIXED. Two independent, complementary fixes now both land on
current `main`, verified together against a freshly rebuilt seed
(`cargo build -p simple-driver --bin simple` — a scoped seed build, not a
full `bin/simple build bootstrap`):

1. `src/compiler_rust/compiler/src/compilability.rs::return_type_keeps_boxed()`
   gained a `Type::Array` arm (landed at commit `cfe0506e336`, already on
   `main` before this session started). This keeps any `InterpCall` whose
   declared return type is `[T]` boxed instead of stripped to a raw i64 —
   the general-shape fix for array-returning `rt_*`/`spl_*` externs still
   routed through the interpreter bridge.
2. **Correction to this doc's original root-cause claim:** a re-check during
   this session found `rt_tls13_sha256` is **no longer** interpreter-table-only.
   `nm -D` on the freshly built seed shows a genuine global `T rt_tls13_sha256`
   symbol (same shape as `T rt_text_to_bytes`), because
   `src/compiler_rust/runtime/src/value/sffi/hash/sha256.rs:112` now defines
   `pub extern "C" fn rt_tls13_sha256(data: RuntimeValue) -> RuntimeValue`,
   registered via `RuntimeFuncSpec::new("rt_tls13_sha256", &[I64], &[I64])`
   (`codegen/runtime_sffi.rs:450`) and `common/src/runtime_symbols.rs:941`.
   That native implementation landed in the bulk commit `969c1f013c3`
   ("chore: sync x25519mlkem768 web/browser and runtime migration") —
   unrelated in its commit message to this bug, but load-bearing for it.
   **This means the JIT now links `rt_tls13_sha256` as a direct native call
   and never routes it through `InterpCall`/`compile_interp_call` at all** —
   fix (1) above is defense-in-depth for other array-returning interpreter-only
   externs, not the mechanism that actually fixes JIT calls to this specific
   symbol today. Confirmed by sabotage: temporarily forcing
   `Type::Array => false` in `return_type_keeps_boxed` and rebuilding the seed
   had **zero effect** on the probes below — both engines still reported
   `len=32` — because that code path is no longer reached for this symbol.
3. **New this session**, narrow defense-in-depth per the "Suggested next
   step" below:
   `src/compiler_rust/runtime/src/value/sffi/value_ops.rs::rt_value_raw_i64`
   now panics (process abort, `extern "C"` panics can't unwind) instead of
   silently returning `0` when handed a non-float heap-boxed value. This is
   the exact fallback site that manufactured the original silent `len=0`: had
   it existed before the `Type::Array` fix, the JIT arm would have crashed
   loudly instead of printing a false `PROBE VERDICT: PASS` with an empty
   digest. Proven with a subprocess-based Rust test (`raw_i64_guard_tests` in
   the same file) that asserts the child process aborts with this message on
   stderr; scalar/bool/nil unboxing is unaffected (also asserted).

Independently reproduced this session: FIPS 180-4 KAT 3/3 PASS on both `jit`
and `interpret`, byte-identical first byte `0xba`, via the exact repro
commands below against the freshly rebuilt seed.

**Not yet deployed to the self-hosted binary** — the live `bin/simple` is the
self-hosted binary, not this Rust seed, so fix (1)/(2) only take effect there
once the self-hosted compiler's own bridge
(`src/compiler/80.driver/compilability.spl`, which has no equivalent predicate
today) gets the same fix or a bootstrap chain from a rebuilt seed picks it up.
Until then, **keep the length-guard fallback** in
`src/lib/common/crypto/sha256.spl:197` — do not remove it on the strength of
this fix alone; only revisit after a real bootstrap redeploy (out of scope
here).
**Found:** 2026-08-05
**Severity:** HIGH — silent wrong-answer in a crypto digest channel, exit 0
**Component:** `rt_tls13_sha256` runtime binding under the Cranelift JIT;
surfaces through `src/lib/common/crypto/sha256.spl:197` (`sha256_text`)

## Verification (this session)

```
SEED=src/compiler_rust/target/debug/simple   # cargo build -p simple-driver --bin simple

SIMPLE_EXECUTION_MODE=interpret $SEED run src/app/test/x25519mlkem768_sha256_extern_probe.spl
  # PROBE tls13_sha256 len=32 / first_byte=186 / VERDICT: PASS
SIMPLE_EXECUTION_MODE=jit       $SEED run src/app/test/x25519mlkem768_sha256_extern_probe.spl
  # PROBE tls13_sha256 len=32 / first_byte=186 / VERDICT: PASS  (was len=0 before)

SIMPLE_EXECUTION_MODE=interpret $SEED run src/app/test/jit_tls13_sha256_fips_kat_probe.spl
SIMPLE_EXECUTION_MODE=jit       $SEED run src/app/test/jit_tls13_sha256_fips_kat_probe.spl
  # both: KAT empty/abc/56byte all match published FIPS 180-4 vectors, 3/3 PASS
```

`cargo test -p simple-runtime` and `cargo test -p simple-compiler` scoped
suites pass (see this doc's git history / session notes for exact test names:
`raw_i64_guard_tests::*` in `value_ops.rs`,
`array_returning_extern_keeps_its_interp_call_result_boxed` in
`compilability.rs`).

## Blast radius beyond `sha256_text` (checked, not deeply audited)

`src/lib/nogc_async_mut_noalloc/tls/{client,transcript}.spl` and
`src/os/apps/sshd/ssh_session_kex.spl` call `rt_tls13_sha256` **directly**,
not through `sha256_text`, so they never had the length-guard fallback and
would have silently used empty/wrong digests under the JIT for the whole
lifetime of this bug. They are fixed by the same root-cause fix (the native
symbol / boxed InterpCall path both now return the correct digest), but were
not independently re-verified end-to-end (TLS/SSH handshake) in this session —
flagging honestly rather than claiming full verification.

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
