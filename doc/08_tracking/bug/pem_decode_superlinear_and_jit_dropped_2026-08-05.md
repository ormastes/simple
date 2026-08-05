# PEM/base64 decode is superlinear, and the whole module never JIT-compiles

**Status:** PARTIALLY FIXED — accumulator fixed; dominant cause OPEN
**Found:** 2026-08-05
**Component:** `src/lib/common/crypto/pem.spl`, plus HIR lowering
(`src/compiler_rust/compiler/src/hir/lower/expr/access.rs:400`)
**Impact:** x509/TLS certificate parsing. 14 s to parse a ~12 KB PEM.

## Measured

Wall clock, timed externally around separate processes (in-language benchmarks
in this repo have been shown to fabricate numbers):

| base64 chars | wall |
|---|---|
| 4,000 | 1.70 s |
| 8,000 | 4.17 s |
| 16,000 | 14.01 s |

Doubling the input more than doubles the time — superlinear.

## What was fixed

`_b64_decode_to_u8` built its filtered character string with
`clean = clean + ch` in a loop. Text is a value type, so each `+` copied the
whole accumulator, making the strip pass quadratic in body length. Replaced with
`kept.push(ch)` and a single `join("")`.

**Correctness proven, not assumed** — RFC 4648 §10 vectors, all six exact:

    Zg==     -> [102]                     f
    Zm8=     -> [102,111]                 fo
    Zm9v     -> [102,111,111]             foo
    Zm9vYg== -> [102,111,111,98]          foob
    Zm9vYmE= -> [102,111,111,98,97]       fooba
    Zm9vYmFy -> [102,111,111,98,97,114]   foobar

These are published standard vectors. No expected value was hand-invented — this
repo has shipped a fabricated ed25519 KAT and a fabricated BIP39 vector.

**Effect: ~10%.** Interleaved A/B at 16,000 chars, alternating OLD/NEW to cancel
load drift on a busy 32-core box:

| round | OLD | NEW |
|---|---|---|
| 1 | 14.78 s | 12.67 s |
| 2 | 13.29 s | 12.49 s |
| 3 | 15.20 s | 13.68 s |

NEW wins 3/3; means 14.42 s vs 12.95 s.

**A first, non-interleaved comparison suggested NEW was 1.6x SLOWER. That was
pure load artifact** — three agents were competing for cores between the before
and after runs. Never compare a before-run against an after-run taken minutes
apart on a loaded box; interleave.

## The dominant cause, still OPEN

10% is far too small for removing a dominant quadratic term. The reason is in
every run log, including the original benchmark:

```
[jit-fallback] HIR lowering error: Unsupported feature: cannot infer field type
  while lowering <fn>: struct 'PemBlock' field 'der_bytes':
  whole module dropped to the interpreter (expect ~100-1000x slowdown)
```

`PemBlock` is `label: text` + `der_bytes: [u8]` (`pem.spl:15-18`). The lowering
gives up on the `[u8]` field, so **the entire module runs interpreted** — every
measurement above, OLD and NEW alike, was taken inside a 100-1000x penalty. The
accumulator fix is a real improvement inside that penalty, not a fix for it.

Diagnostic emitted at
`src/compiler_rust/compiler/src/hir/lower/expr/access.rs:400`. The neighbouring
comment at `:184` attributes it to **field-access-on-ANY**, so the trigger is an
erased receiver at the access site, not the `[u8]` declaration by itself.

### Blast radius — an UPPER BOUND, not a measured count

`^\s+<name>\s*:\s*\[u8\]` matches **812 field declarations across 297 files**
under `src/lib/` and `src/os/`, including `x509.spl`, `x25519_mlkem768/contract.spl`,
`aes128_ccm.spl`, `aes256_ccm.spl`, `argon2.spl`, `dual_backend.spl`, and both
`pem.spl` files.

**Do not report 297 as the number of JIT-dropped modules.** The grep approximates
a bound rule: declaring a `[u8]` field is not sufficient to trigger the drop —
only an erased-receiver field access is. `pem.spl` is the one module measured to
drop. Establishing the true count requires running each candidate and grepping
its log for `jit-fallback`, which has not been done.

## Next step

Fix the HIR lowering so a `[u8]` struct field does not force the module
interpreted, then re-measure PEM decode. That is where the 100-1000x is. Until
then the remaining superlinearity in `_b64_decode_to_u8` (four `clean.char_at()`
calls per 4-char group, plus `alphabet.index_of(ch)` per character) is not worth
optimising — it is noise against the interpreter penalty.

## Reproduce

```
# build a PEM with N*16 base64 chars, parse it, time externally
timeout 400 env SIMPLE_TIMEOUT_SECONDS=0 ./bin/simple run <driver>.spl
grep -a 'jit-fallback' <log>   # confirms the module ran interpreted
```

Score wall clock from outside the process. `SIMPLE_TIMEOUT_SECONDS=0` is required
or a ~60 s CPU guard kills the 16,000-char run at exit 143 and it reads as a
failure.
