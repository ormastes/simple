# Seed reportedly rejects one-line `elif c: x = v` (not reproducible)

- Date: 2026-11-27
- Status: verification-pending (could not reproduce; prevention tests landed)
- Area: seed parser (`src/compiler_rust/parser`), pure-Simple parser
  (`src/compiler/10.frontend/core/parser_stmts.spl`)
- Reported by: hello-sanity buildrunner twin lane

## Report

A lane said the seed rejects a one-line `elif` arm that holds an assignment,
`elif c: x = v`, and guessed that the pure-Simple parser accepts it.

## Repro attempt

```
fn f(c: i64) -> i64:
    var x = 0
    if c == 1: x = 10
    elif c == 2: x = 20
    else: x = 30
    x
```

Variants also tried: a block then-arm followed by an inline elif, an inline elif
after a nested inline `if`, index/field/compound-assign targets, `if val`/`elif val`,
same-line `if c: x = 1 elif d: x = 2`, a class method, and module level.

| Parser | Binary / source | Result |
|---|---|---|
| Seed | `C:/dev/wt/bound3x-target/release/simple.exe` (2026-11-26 03:55) | accepts; correct values |
| Seed | `C:/dev/simple/bin/simple.exe` (2026-11-19 19:22) | accepts; correct values |
| Pure-Simple | `parser_stmts.spl` if/elif collector, driven by `parse_statement` | accepts; each elif arm is an `STMT_ASSIGN` |

The syntax quick reference treats inline `if`/`elif`/`else` arms as legal, so
accepting this form is the intended behaviour. Nothing needs to change in either
parser. The lane most likely hit a different shape or an older seed. If it
happens again, attach the exact source line and the binary's hash.

Side observation, not part of this bug: one probe that also used a dict literal
index (`x = {"k": 1}["k"]`) timed out after 60 s in the seed interpreter. It is not
an `elif` issue and is not triaged here.

## Prevention

- Rust: `src/compiler_rust/parser/src/elif_inline_assign_test.rs`, 5 cases,
  registered in `lib.rs`. `cargo test -p simple-parser --lib elif_inline_assign`
  gives 5 passed.
- Simple: `test/01_unit/compiler/parser/elif_inline_assign_spec.spl`. Runtime
  witnesses pin the executing (seed) parser. Structural checks pin the pure-Simple
  parser, plus a non-vacuity probe that a plain `if` reports no elif arm. Result:
  6/6 pass on the seed.
