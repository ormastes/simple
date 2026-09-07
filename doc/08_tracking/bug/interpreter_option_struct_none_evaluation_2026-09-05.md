# Interpreter lane fails on ANY evaluation of a None-valued `Option<struct>`

**Date:** 2026-09-05
**Found by:** sspec score-80 wave 8D (modernizing `test/system/coupling_analysis_spec.spl`)

## Symptom

On the interpreter lane (Sep-5 seed
`src/compiler_rust/target/bootstrap/simple run`), evaluating a
`Option<struct>` value that is **None** fails with:

```
semantic: class 'Option' not found in this scope
```

in EVERY evaluation form tried: `if val Some(w) = ...`, truthiness
(`if opt:`), `match`, and even `opt != nil`. Some-valued paths work, and
`Option<i64>` None paths work — only the None payload of a
struct-parameterized Option breaks.

The JIT/native lane is unaffected.

## Impact

`test/system/coupling_analysis_spec.spl` had to be shaped around this:
below-threshold W-rule halves assert through array-returning APIs
(`find_cycles`, `find_layer_violations`, `find_instability_inversions`,
metrics) instead of pattern-matching None lint results. Any spec that
pattern-matches an absent lint finding on a struct Option cannot run on
the interpreter lane.

## Repro shape

```simple
# against compiler.semantics.lint.coupling, or any fn returning Option<SomeStruct>:
val hit = find_layer_violation(<below-threshold input>)   # returns None
if hit != nil:        # <- semantic: class 'Option' not found in this scope
    expect(false).to_equal(true)
```

## Unblock condition

`opt != nil` (and `if val Some(w) =`, truthiness, `match`) on a
None-valued `Option<struct>` evaluates without a semantic error on the
interpreter lane; then the W-rule halves in
`test/system/coupling_analysis_spec.spl` (and its eventual twin) can be
re-pointed at direct None-matching.
