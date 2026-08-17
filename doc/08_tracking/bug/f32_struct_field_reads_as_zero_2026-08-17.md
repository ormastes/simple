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

---

## RESOLVED 2026-08-17 — store width disagreed with load width on three paths

Root cause is NOT boxing. `compile_field_get`
(`src/compiler_rust/compiler/src/codegen/instr/fields.rs`) loads each struct
field at the slot's **declared** cranelift width — 4 bytes for `f32` — while
every store path wrote the value at whatever width the *source* carried.
Storing an f64 and loading 4 bytes back is a bit **truncation**, not a numeric
conversion:

```
2.5f64 = 0x4004000000000000 -> low 32 bits are zero  -> reads back 0.0
0.1f64 = 0x3FB999999999999A -> low 32 bits 0x9999999A -> reads back
                                -0.000000000000000000000015881868392106856
```

The `0.1` case is the discriminating measurement: only a low-half
reinterpretation produces that exact negative denormal, which rules out an
uninitialised slot or a zeroing store.

### Engines

| engine | before | after |
|---|---|---|
| tree-walk interpreter (`SIMPLE_EXECUTION_MODE=interpreter`) | **CORRECT** (`2.5`) | correct |
| cranelift JIT (`SIMPLE_EXECUTION_MODE=jit`, the default for `run`) | **WRONG** (`0.0`) | correct |
| llvm native | not separately exercised; the fix is in the shared MIR lowering (path 2 below) plus the cranelift-only paths 1 and 3 |

The bug doc's suspicion that the pure-Simple self-hosted compiler might diverge
remains **UNVERIFIED**: `bin/simple` resolves to the Rust seed on this host and
the lane must not redeploy it, so no self-hosted binary was available to probe.

### Fix (commit `ac438753ebb`)

1. `codegen/instr/closures_structs.rs` — `widen_struct_field_value` handled only
   integers, so a float fell through unchanged. It now `fdemote`/`fpromote`s to
   the declared width. This is the constructor path (`S(a: 2.5)`).
2. `mir/lower/lowering_stmt.rs` — `MirInst::FieldSet` was lowered with the
   **right-hand side's** type while `FieldGet` is lowered with the field-access
   expression's type (`lowering_expr_struct.rs`, `field_type: expr_ty`). Traced
   directly: `[TRACE FieldSet] byte_offset=0 field_type=TypeId(11) val_ty=F64`
   against `[TRACE FieldGet] byte_offset=0 field_type=TypeId(10)` for the same
   field. `FieldSet` now uses `target.ty`, the same type `FieldGet` uses.
3. `codegen/instr/fields.rs` — `compile_field_set` coerces the value to the
   field slot's type (float demote/promote, integer narrowing) so the store
   width always equals the load width.

Paths 1 and 2 are each independently sufficient to keep the bug alive: fixing
only 1 left `s.a = 7.5` reading `0.0`.

### Evidence

Reproduce-first, on the bug doc's own repro, cranelift JIT:

```
before: 0.0    3.5    2.5        (s.a wrong, s.b and the f32 local fine)
after:  2.5    3.5    2.5
before: -0.000000000000000000000015881868392106856   (0.1 into an f32 field)
after:  0.10000000149011612
```

Specs (reproduce-first: RED on the unfixed binary, GREEN on the fixed one):

```
unfixed: Results: 5 total, 4 passed, 1 failed
         ✗ agrees between the interpreter and the cranelift JIT on every f32 field read
fixed:   SPEC FILE VERDICT: .../f32_struct_field_roundtrip_spec.spl declared>=5 executed=5 passed=5 failed=0 dropped=0
         Results: 5 total, 5 passed, 0 failed
         SPEC FILE VERDICT: .../struct_field_width_roundtrip_spec.spl declared>=5 executed=5 passed=5 failed=0 dropped=0
         Results: 5 total, 5 passed, 0 failed
```

### Specs shipped (commit `c096b20ffc9`)

- Reproducing: `test/01_unit/compiler/codegen/f32_struct_field_roundtrip_spec.spl`
  (mirror: `test/unit/compiler/codegen/f32_struct_field_roundtrip_spec.spl`)
- Prevention/generalization:
  `test/01_unit/compiler/codegen/struct_field_width_roundtrip_spec.spl`
  (mirror: `test/unit/compiler/codegen/struct_field_width_roundtrip_spec.spl`)

The prevention spec generalizes past `f32` to the actual defect class — every
declared field width (`f32`/`f64`/`i32`/`u8`) through every store path
(constructor, assignment, array element). Both specs cross-check the
interpreter against the JIT in a subprocess, because a spec file falls back to
the interpreter and the in-process examples therefore could never have been red.
`SIMPLE_BIN` points the subprocess arm at a candidate binary; it defaults to
`bin/simple`, so the JIT arm stays red until the fixed seed is deployed.

### Not closed by this change

`test/03_system/game3d/rollball_production_spec.spl` was listed as a likely
second victim but was not confirmed against this root cause here.
