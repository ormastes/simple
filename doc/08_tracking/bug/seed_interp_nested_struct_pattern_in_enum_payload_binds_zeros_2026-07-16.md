# Seed interpreter: nested struct pattern inside enum payload binds all fields to 0

- **Date:** 2026-07-16
- **Component:** Rust seed interpreter (`bin/simple run`, SIMPLE_BOOTSTRAP unset)
- **Status:** OPEN (seed-side; not fixable from pure-Simple source)
- **Found by:** native-build correctness campaign, parity case `nested_enum_struct_match`
  in `scripts/check/check-native-seed-parity.shs`

## Symptom

```spl
struct Point:
    x: i64
    y: i64

enum Shape:
    Circle(Point)
    Empty

fn main() -> i64:
    val s = Shape.Circle(Point(x: 3, y: 5))
    match s:
        case Shape.Circle(Point(x, y)): print(x * 10 + y)
        case Shape.Empty: print(99)
    return 0
```

- Seed `run`: prints `0` — the `Circle` arm IS taken (an `Empty` arm printing 99
  proves arm selection is correct), but the nested struct pattern binds
  `x = 0, y = 0`.
- Pure-Simple `native-build`: prints `35` (correct; verified with a second value
  set `Point(x: 4, y: 7)` -> `47`, so binding is real, not accidental).

## Workaround

Bind the payload whole and use field access — `case Shape.Circle(p): p.x ... p.y`
works correctly in the seed.

## Class

Same bind-zeros landmine class as the seed's `case (a, b):` tuple pattern
(parity case `tuple_pattern_match`, already NATIVE-AUTHORITATIVE).

## Harness impact

`nested_enum_struct_match` reclassified PARITY -> NATIVE-AUTHORITATIVE
(expected `35`) in `check-native-seed-parity.shs` on 2026-07-16, since the seed
oracle is provably broken here and the seed is Rust (rebuild forbidden in the
native-build campaign; fix belongs in `src/compiler_rust` interpreter pattern
binding when the seed is next rebuilt).

## Verification (2026-07-16)

Still reproduces at origin tip 8932fcb3a148: `probe12_nested_struct_pattern_a.spl` (doc's exact repro: `Shape.Circle(Point(x:3,y:5))` matched via `case Shape.Circle(Point(x, y)): print(x*10+y)`). Oracle: `bin/simple run` → `0` (should be `35`). Nested struct pattern binds `x=0, y=0` instead of real field values; matches seed landmine exactly, still OPEN.
