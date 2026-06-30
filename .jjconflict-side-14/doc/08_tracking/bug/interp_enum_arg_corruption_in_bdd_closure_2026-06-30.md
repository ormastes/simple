# Bug: enum value corrupted when passed as a function arg inside a BDD it-closure

- Date: 2026-06-30
- Component: interpreter / test runner (BDD it-block closure evaluation)
- Severity: medium (breaks otherwise-correct specs; not a library defect)
- Status: OPEN — needs seed fix (cannot be worked around in pure-Simple)

## Symptom

In `test/01_unit/lib/common/compress_utilities_spec.spl`, the example
"reports the runtime-selected tier with a stable public name" fails:

```
expected avx2 to equal neon
```

The spec computes a payload-less enum value, passes it to a helper, then
compares it with `==`:

```
val detected = compression_simd_tier_detect()          # CompressionSimdTier.avx2 on this host
val name = compression_simd_tier_name(detected)         # "avx2"  (correct)
if detected == CompressionSimdTier.scalar: ...
elif detected == CompressionSimdTier.avx2: ...          # NOT taken (bug)
else: expect(name).to_equal("neon")                     # taken -> fails
```

`detected` is genuinely `avx2` (the prior `.to_equal` assertion passes and
`compression_simd_tier_name(detected)` returns `"avx2"`), yet the subsequent
`detected == CompressionSimdTier.avx2` evaluates false **inside the it-block**.

## Root cause (isolated via minimal repros)

The same code runs correctly under `bin/simple run` (enum `==` and detect both
correct). The failure is specific to BDD it-block closure evaluation in the
test runner, in BOTH default and `SIMPLE_EXECUTION_MODE=interpret` modes.

Minimal probes show: passing a payload-less enum value as a **function
argument** inside an it-closure corrupts the caller's binding of that value
(subsequent `==` comparisons return wrong results). The corruption fires even
when:
- the callee ignores the argument entirely, and
- the comparison bool is computed and stored *before* the offending call.

This points to the interpreter mutating/writing back the (likely
globally-interned) enum variant when it crosses a call boundary inside a
closure — the same family as the documented "method-call result passed as an
arg corrupts under a nested interpreter" and "lambda arg-mutation written back
to caller" interpreter behaviors.

## Impact

`compress_utilities_spec` is 10/11; this single example is blocked. The
underlying library code (`compression_simd_tier_detect/_name/_from_simd_profile`)
is correct — verified standalone.

## Fix direction

Fix in the seed interpreter: enum (and nullable) values must be passed by value
across call boundaries inside closures without writing a corrupted value back to
the caller / mutating the shared variant singleton. No pure-Simple workaround
exists without rewriting the spec's (correct) assertion logic, which would mask
the bug.
