# Interpreter: sequential `if X: return Y` only first branch fires

**Status:** RESOLVED (2026-05-03). No longer reproducible in current binary.
Regression spec added: `test/unit/compiler/sequential_if_return_spec.spl` (8/8 PASS).
**Path:** `bug` track. Interpreter.

## Symptom

In interpreter mode, a sequence of independent `if` statements where each
contains a `return`:

```spl
fn classify(b64: u8) -> i64:
    if b64 == 0x41u8: return 0
    if b64 == 0x42u8: return 1
    if b64 == 0x43u8: return 2
    return -1
```

…only the FIRST `if` branch fires. Calls with `b64 == 0x42u8` or `b64 == 0x43u8`
fall through every later branch and return -1, instead of 1 or 2.

W18-K SCRAM-SHA-256 hit this in its base64 alphabet classifier; the function
was rewritten to a single nested `if`/`elif` chain, which works.

## Reproduction

```spl
fn first_match(x: i64) -> i64:
    if x == 1: return 10
    if x == 2: return 20
    if x == 3: return 30
    return -1
```

Interpreter mode: `first_match(2)` returns `-1` instead of `20`.
Compile mode: `first_match(2)` returns `20` correctly.

This is documented in memory `feedback_simple_parser_strict_callsites.md` as
one of the interpreter strict-callsite issues but not yet filed as a standalone
bug.

## Root cause hypothesis

The interpreter's statement-list evaluator likely consumes the explicit `return`
control-flow only once — subsequent `if` statements with `return` are treated as
"already evaluated; skip". OR: the if-statement evaluator in the interpreter
folds a sequence of `if`s into a single `if-elif-else` chain at parse time, but
loses the `return` semantics for branches 2..N.

Suspect file:
- `src/compiler_rust/compiler/src/interpreter/...` statement evaluator
- HIR lowering for `if` may merge statements with implicit jumps

## Workaround (current)

Rewrite as nested `if`/`elif`:

```spl
fn classify(b64: u8) -> i64:
    if b64 == 0x41u8:
        return 0
    elif b64 == 0x42u8:
        return 1
    elif b64 == 0x43u8:
        return 2
    else:
        return -1
```

Or use a base64-decode helper instead of inline alphabet classification.

## Affected sites

- W18-K SCRAM-SHA-256 base64 classifier (workaround applied)
- Memory `feedback_simple_parser_strict_callsites.md`
- Possibly any handcoded byte/codepoint classifier

## Verification

Add a probe spec at `test/unit/compiler/interpreter_sequential_if_return_spec.spl`
exercising the minimal case. Expected: 3/3 PASS in compile mode, 1/3 in
interpreter mode.

## Cross-references

- `feedback_simple_parser_strict_callsites.md`
- W18-K SCRAM-SHA-256 commit (search session log for "SCRAM" + "elif")
- Bug `it_block_var_mutation_lost_2026-05-01.md` — related interpreter
  control-flow corruption pattern
