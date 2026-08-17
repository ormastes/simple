# f32 struct fields always read back as 0.0

- **Date:** 2026-08-17
- **Status:** OPEN
- **Severity:** HIGH — silently wrong numerics, no error, no warning
- **Found by:** `test/03_system/` sweep (test/03_system/game_net, test/03_system/game3d)

## Symptom

A struct field declared `f32` reads back as `0.0` no matter what was stored.
`f64` fields are unaffected, and a plain `f32` local is unaffected — the loss is
specific to the *struct field* path.

## Minimal repro

```simple
struct S:
    a: f32
    b: f64

fn main():
    val s = S(a: 2.5, b: 3.5)
    print s.a        # prints 0.0   <-- WRONG, expected 2.5
    print s.b        # prints 3.5   (correct)
    val x: f32 = 2.5
    print x          # prints 2.5   (correct)
```

Run: `bin/simple run repro.spl`

The same zeroing is observed for nested structs (`o.i.a`) and for struct
elements read out of an array (`arr[0].a`), which are just the same field read
one level down — those are consequences, not separate defects.

## Impact — how it was found

`bin/simple test test/03_system/game_net/netcode_prediction_spec.spl` fails 4 of
9, e.g.:

```
✗ dropped input frame recovered via next ack + replay
    expected 0.0 to equal 2.5
```

`src/lib/nogc_sync_mut/game_net/demo_sim.spl` stores positions in `SimState`
as `f32`. The integrator itself is correct (the sequence numbers it acks are
right), but every `pos_x` read back through `SimState`/`EntityState` comes out
`0.0`, so every absolute-position oracle in the netcode slice fails. The
`2.5` in the failure message is exactly 5 ticks x 0.5, i.e. the spec's
arithmetic is right and only the field read is wrong.

`test/03_system/game3d/rollball_production_spec.spl` (1/1 failing) is a
likely second victim — same f32-position shape — but has not been confirmed
against this root cause.

## Notes for whoever fixes it

- Reproduced on the binary that `bin/simple` currently points at, which
  announces itself as the **Rust bootstrap seed**. Whether the pure-Simple
  self-hosted compiler has the same defect is UNVERIFIED — check both before
  closing, since the seed and the self-hosted lowering are separate code.
- Likely area: f32 boxing/unboxing in struct field get/set. `f64` surviving
  while `f32` zeroes points at a missing 32-bit float case in the value
  encode/decode path rather than at the struct layout itself.
- Adjacent, already-filed float defects that may share a cause:
  `float_returning_method_in_argument_position_prints_tagged_bits_2026-08-10.md`,
  `gpu_memset_f32_discards_value_and_no_f32_bitcast_2026-08-06.md`.

## Regression spec

Deliberately NOT landed with this report: a spec asserting `s.a == 2.5` is red
today, and landing a known-red spec on `main` would block unrelated lanes. The
fixing change must ship it — the repro above plus a generalization covering
`f32` direct, nested, and array-element field reads, mirror-synced and citing
this document.
