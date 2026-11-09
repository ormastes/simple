# JIT `to_i32()` returns 0 for characters and leaks mis-tagged values for literals
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-08-26
**Area:** JIT / codegen dispatch for the `to_int`/`to_i64`/`to_i32`/`to_i16`/`to_i8`
string-method family
**Status:** OPEN
**Sibling:** `char_to_i32_input_independent_zero_2026-08-26.md` (the INTERPRETER
half, fixed). This record is the JIT half, which that fix does NOT reach.

## Symptom

Same binary (a seed built 2026-08-26 carrying the interpreter fix), same probe,
only `SIMPLE_EXECUTION_MODE` differs:

| expression | `SIMPLE_EXECUTION_MODE=interpreter` | default (JIT) |
|---|---|---|
| `for ch in "hello": print(ch.to_i32())` | `104 101 108 108 111` | `0 0 0 0 0` |
| `for ch in "world": print(ch.to_i32())` | `119 111 114 108 100` | `0 0 0 0 0` |
| `"5".to_i32()` | `5` | `<value:0x5>` |
| `"a".to_i32()` | `97` | `0` |
| `"42".to_i32()` | `42` | `0.000…0002` (float-shaped, ~300 digits) |

## Why this is worse than a wrong number

`<value:0x5>` is a value rendered through the WRONG TAG — the payload `5` is
right, the tag says it is not an integer. `"42".to_i32()` printing a
float-shaped 300-digit string is the same failure with a different mis-tag. So
this is not "the parse fell back to 0"; it is a value-representation defect on
the JIT dispatch path, in the same family as the tagged-value seam faults
already tracked for Stage 3.

## Consequence

Every checksum or hash that folds `ch.to_i32()` per character is STILL
degenerate under the default execution mode, which is what `bin/simple run`
uses. Fixing the interpreter arm alone does not make such a hash correct in
production; it only makes it correct under an explicitly-set env var.

## Reproduce

    cat > probe.spl <<'SPL'
    fn main():
        for ch in "hello":
            print(ch.to_i32())
        print("5".to_i32())
        print("42".to_i32())
    SPL
    simple run probe.spl                                  # JIT: 0 0 0 0 0, <value:0x5>, float-shaped
    SIMPLE_EXECUTION_MODE=interpreter simple run probe.spl # 104 101 108 108 111, 5, 42

A discriminating pair, not a single observation: the two modes disagree on the
SAME binary, so the defect cannot be attributed to a stale artifact.

## Where to look

The interpreter arm lives in
`src/compiler_rust/compiler/src/interpreter_method/string.rs` (the
`"to_int" | "to_i64" | "to_i32" | "to_i16" | "to_i8"` match). The JIT reaches
this method by a different route, and that route is what needs finding — start
by establishing whether it dispatches to a builtin (as `d[k]` on a class field
was found to do in a previous defect) rather than to the user-visible method at
all.

## Prevention

This is exactly what `check-engine-differential` exists to catch: a `run`
-vs-interpreter divergence on identical source. Add this probe as an
engine_differential fixture, which is the only place such a divergence can be
pinned. Note that gate is currently reported BLIND (`ERROR — nothing was
checked`) on a stale seed, so the fixture will not produce a verdict until a
redeploy — record the failing-first observation in the fixture header meanwhile.



## 2026-11-09 — FIXED on work/p3-subj4-seed-20261109 (fresh cargo build of release/1.0.0 source, aarch64)

Reproduced RED on a seed built from current `origin/release/1.0.0` source
(the deployed Nov 5 binary shows the same symptoms, so the defect was live in
source, not just a stale artifact):

- JIT: `for ch in "hello": print(ch.to_i32())` -> `0 0 0 0 0`;
  `print("5".to_i32())` -> `<value:0x5>`; `print("42".to_i32())` -> the f64
  denormal of bit pattern 42 (~300 digits).
- Interpreter (same binary): `104 101 108 108 111`, `5`, `42`.

Root cause, two independent defects:

1. **Mis-tagged print**: the HIR string-receiver result-type table
   (`src/compiler_rust/compiler/src/hir/lower/expr/mod.rs`) typed
   `to_int`/`to_i64` as `I64` but omitted `to_i8`/`to_i16`/`to_i32`. Those
   calls fell through to ANY-typed generic dynamic dispatch, so MIR
   print-lowering emitted no `BoxInt` and the raw narrowed word reached
   `rt_println_value`, which decoded it by bit pattern. Arithmetic on the
   same value was always correct — only the tag was missing.
2. **Char codepoints**: `rt_string_to_int`
   (`src/compiler_rust/runtime/src/value/collections.rs`) lacked the
   single-character CODEPOINT fallback the interpreter arm received in
   8d100a8aa81, so every non-digit character folded 0 under the default JIT
   lane.

Fix: added the three i-family entries to the HIR table; added the codepoint
fallback (parse first; on failure a single character yields its codepoint;
multi-character non-numeric still yields 0, exactly like the interpreter).

GREEN evidence (same probe, fresh-built seed, JIT lane):
`104 101 108 108 111 / 5 / 42` — byte-identical to the interpreter.
Cargo pins: `simple-runtime string_to_int_single_char_fallback_tests` (2),
`simple-compiler string_receiver_to_i32_family_result_is_typed_not_any` (1);
40-test `semantic` slice and 5-test `to_int` slice pass.

Known residual (separate lane, NOT fixed here): the C-runtime twin
`rt_string_to_int` in `src/runtime/runtime_native.c` (strtoll-lenient) still
lacks the codepoint fallback, and the interpreter rejects `to_u*` on strings
while the JIT silently mis-computes them — both out of this row's scope.
