# Seed interpreter: `.to_int()` misdispatches on split()-produced strings

## VERIFIED FIXED 2026-08-17 — does not reproduce

Classified by content and execution, not SHA ancestry (brief correction #1).
Executed against the deployed `bin/simple`, default lane:

```
val parts = "10,20,30".split(",")
print(parts[1])                              # => 20
print(parts[1].to_int())                     # => 20   (reported: pointer-like garbage)
print(parts[0].to_int() + parts[2].to_int()) # => 40
```

A `split()`-produced string now dispatches `.to_int()` the same as a literal.
The sum is included so a coincidentally-right single read cannot pass this.

## VERIFIED FIXED 2026-08-17 (batch_02 core-silent-wrong lane) — does not reproduce

The "Minimal repro" below was re-run verbatim and prints `10`, correctly, under
BOTH `SIMPLE_EXECUTION_MODE=interpret` and the default JIT lane, on BOTH the
deployed seed (mtime 2026-08-16 22:59) and a seed freshly built this session
from `88227f48202`:

```
val parts = "10,4".split(",")
val p = parts[0]
print(p.to_int())        -> 10   (doc: pointer-like garbage, e.g. 6277833388737)
```

Same-family evidence: the sibling doc
`seed_jit_string_to_i64_float_tagged_silent_wrong_2026-07-28.md` is also fixed,
by `2a240d9b0b2`, which added the missing STRING receiver branch to the
numeric-cast dispatch — i.e. exactly the "dispatch resolving to a different
method for these receivers" this doc predicted.

Closeable. The Simple-side workaround `core_digits_to_i64`
(`src/compiler/10.frontend/core/lexer.spl`) is now removable, but that removal
is deliberately NOT done here: the lexer is in another lane's claimed path this
session.

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
