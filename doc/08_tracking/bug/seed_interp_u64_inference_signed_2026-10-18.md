# Seed interpreter: unannotated `val` from u64 extern results is treated as signed i64

Date: 2026-10-18. Scope: Rust seed interpreter only (bin/local/seed_simple, sha256 prefix 9c45d2bf601ab93e).
The self-hosted compiler was NOT checked: no pure-Simple CLI is deployed on this host. JIT is unaffected.

## Symptom
`val x = rd(b, 0) ^ rd(b, 8)` where `rd` wraps the `rt_typed_bytes_u64_le_at` extern (declared `-> u64`)
and the result has bit 63 set yields a negative i64 in the interpreter, so `x >> 32u64` is an arithmetic shift
and `x`'s later arithmetic is wrong. With `val y: u64 = ...` the result is correct.
Found while implementing XXH3 (src/lib/common/crypto/xxh3.spl): every input >= 241 bytes hashed wrongly
in spec runs until the u64 locals were annotated.

## Repro
build/probe/u64_infer_bug.spl (10 lines):

    val x = rd(b, 0) ^ rd(b, 8)          # inferred
    val y: u64 = rd(b, 0) ^ rd(b, 8)     # annotated
    print((x >> 32u64).to_text()); print((y >> 32u64).to_text())

    SIMPLE_EXECUTION_MODE=interpreter -> inferred hi=-1352034457  annotated hi=2942932839
    SIMPLE_EXECUTION_MODE=jit         -> inferred hi=2942932839   annotated hi=2942932839

## Narrowing
Not reproduced with plain `fn a() -> u64` literals (`a() ^ b()`), nor with `annotated_u64_val ^ rd(...)`.
Needs the xor of two values produced by the extern-backed function.

## Workaround
Annotate u64 locals explicitly (`val x: u64 = ...`); done throughout xxh3.spl.
