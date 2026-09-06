# Seed interpreter: `.to_int()` misdispatches on split()-produced strings

- **Status:** open (seed/Rust interpreter; worked around in Simple code)
- **Date:** 2026-07-03
- **Component:** `src/compiler_rust` interpreter method dispatch

## Symptom

Under `src/compiler_rust/target/bootstrap/simple run`, `.to_int()` on a
string obtained from `split()` (or in plain assignment position in some
contexts) returns pointer-like garbage (e.g. `6277833388737`) or a float
zero, instead of the parsed integer. The same value used inside a string
interpolation (`"{s.to_int()}"`) parses correctly.

## Minimal repro

```simple
fn main() -> i64:
    val parts = "10,4".split(",")
    val p = parts[0]
    print "{p.to_int()}"   # garbage, expected 10
    return 0
```

The correct implementation exists in
`compiler/src/interpreter_method/string.rs` (`"to_int" => s.trim().parse`),
so dispatch is resolving to a different (wrong) method for these receivers —
likely a name-keyed impl-method lookup that shadows the builtin.

## Impact / workaround

Corrupted the CoreLexer indent-stack save/restore path (see
`stage4_lexer_snapshot_restore_to_int_misdispatch_2026-07-03.md`).
Worked around with a dispatch-free digit parser (`core_digits_to_i64` in
`src/compiler/10.frontend/core/lexer.spl`). Fix belongs in the seed's
method-dispatch order; until then avoid `.to_int()` on runtime-produced
strings in seed-executed hot paths.

## Re-probed 2026-09-06 — NOT REPRODUCIBLE

Binary probed: `bin/release/aarch64-unknown-linux-gnu/simple` (Rust seed,
aarch64). Both engines exercised: `SIMPLE_EXECUTION_MODE=interpret` (tree-walk)
and `env -u SIMPLE_EXECUTION_MODE` (default Cranelift JIT). Probe sources are
listed with each entry; they were run on both lanes and compared.

The record's own minimal repro (`"10,4".split(",")` then `parts[0].to_int()`)
now yields `10` on BOTH lanes:

```
SPLIT_TO_INT=10     # interpret
SPLIT_TO_INT=10     # jit
```

Probe `_scratch/p_str.spl`. Not fixed by this session — it was already correct.
The workaround `core_digits_to_i64` in `src/compiler/10.frontend/core/lexer.spl`
that this record installed can be revisited independently; it was NOT removed
here, since removing a live workaround needs its own verification pass.
