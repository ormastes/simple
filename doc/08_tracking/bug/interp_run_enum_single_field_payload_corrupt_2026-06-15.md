# Bug: `bin/simple run` corrupts single-field enum payload values

**ID:** interp_run_enum_single_field_payload_corrupt_2026-06-15
**Severity:** P1 (data corruption, silent)
**Affected path:** `bin/simple run` (default JIT/interpreter driver, not seed-driven test runner)
**Date:** 2026-06-15

## Symptom

When an enum case has exactly one field, the extracted value is wrong under `bin/simple run`.
The pattern observed: `n >> 3` (right-shift by 3) — e.g. 65→8, 100→12, 255→31, 1→0.

Two-field enum cases (Match(distance, length)) work correctly.

## Minimal repro

```spl
enum Tok:
    Literal(b: i64)
    Other(x: i64, y: i64)

fn main():
    val t = Tok.Literal(b: 65)
    match t:
        case Tok.Literal(b: v):
            print(v.to_text())   # Prints "8", expected "65"
        case Tok.Other(x: x, y: y):
            print("wrong")

    val o = Tok.Other(x: 3, y: 7)
    match o:
        case Tok.Literal(b: v):
            print("wrong")
        case Tok.Other(x: xv, y: yv):
            print(xv.to_text() + " " + yv.to_text())  # Prints "3 7" — correct
```

Run via: `bin/simple run repro.spl`

## Does NOT affect

- `bin/simple test` via seed driver (`SIMPLE_BOOTSTRAP_DRIVER=bin/release/.../simple_seed`) — enum values are correct there.
- Two-field enum cases regardless of driver.

## Also observed in same session

`BitWriter.put_bits` / `BitReader.read_bits` produce wrong byte values under `bin/simple run`:
- `put_bits(1, 1) + align()` → byte[0]=64 (expected 1)
- `put_bits(42, 8)` → byte[0]=128 (expected 42)
- Round-trip readback always 0

These same methods pass all 52 tests in `test/01_unit/lib/common/bytes/bits_spec.spl` under the seed test runner. The `me`-method self-mutation on `BitWriter.acc`/`nbits` appears lost between iterations under `bin/simple run`.

## Proposed fix area

- Interpreter enum payload extraction in `src/compiler_rust/` — look for field offset calculation off by 3 bits for single-field variants.
- `me`-method mutation: `self.field = ...` inside while-loop body may not commit back to the struct in run/JIT mode.

## Workaround

Use `bin/simple test` with `SIMPLE_BOOTSTRAP_DRIVER` for all enum + me-mutation testing.
Do NOT use `bin/simple run` to verify numeric payload values from enum cases with 1 field.
