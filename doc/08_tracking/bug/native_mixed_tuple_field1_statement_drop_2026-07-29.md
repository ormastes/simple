# Native lane: reading field 1 of a mixed (text, i64) tuple silently drops statements

**Status:** open — found (and separated from the optional-extraction bug)
while validating the Some-binding fix. Pre-existing: the deployed seed
exhibits it MORE broadly than the patched debug seed.
**Severity:** silent statement drops on the DEFAULT engine — a `print`
interpolating the i64 field of a mixed tuple simply does not execute, and
inside an if-val then-block every statement FROM that point is skipped,
with control resuming after the if. No diagnostic, exit code 0.

## Repro (native `bin/simple run`, no JIT-fallback line)

```
fn plain() -> (text, i64):
    ("y", 8)

fn main():
    print "A"
    val t = ("x", 7)
    print "LOCAL1: {t.1}"    # SILENTLY DROPPED
    print "B"
    val u = plain()
    print "RET1: {u.1}"      # SILENTLY DROPPED
    print "C"
```

Patched debug seed (2026-07-30): prints A, B, C — both `.1`
interpolations vanish. Deployed seed: even worse — on a variant of this
probe every marked print vanished. Homogeneous tuples are fine:
`(i64, i64)` interpolates both fields correctly (T0=5 T1=9), and
`match Some(t)` over `(i64, i64)?` binds and prints 5 9 after the
optional-extraction fix. Only the MIXED (text, i64) tuple's non-zero
field is affected. Comparisons read garbage too: `parts.1 == 7` on a
decode result whose consumed count IS 7 evaluates false.

## Suspected locus

Tuple element typing/layout for heterogeneous tuples in the seed's
MIR/codegen: field 1's load is likely typed/boxed as the wrong element
class (text pointer vs raw i64), and the interpolation/compare path traps
or mis-lowers, with the trap surfacing as a silent skip of the remaining
statements in the enclosing block rather than an error.

## Impact

- The historical "if-val Some((text,i64)) skips BOTH branches" symptom in
  the optional-extraction bug was partly THIS: the then-branch was
  entered, but its single print interpolated `.1` and everything from
  there was dropped.
- MQTT decode round-trip: decoded VALUE is correct natively after the
  optional fix; the (value, consumed) tuple's consumed count cannot be
  read natively until this is fixed.

## Notes

- Spec-lane regression coverage is impossible today (interpreter lane is
  correct); keep the repro above for native re-verification.
- Do not conflate with the optional-extraction bug (fixed) or the
  kafka <<3 tag-box family; this one is specific to heterogeneous tuple
  field access.
