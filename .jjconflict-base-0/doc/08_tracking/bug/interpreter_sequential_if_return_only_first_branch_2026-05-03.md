# Interpreter: sequential `if X: return Y` only first branch fires

Status: RESOLVED (2026-05-03). No longer reproducible in current binary.

**Status:** RESOLVED (2026-05-03). No longer reproducible in current binary.
Regression spec added: `test/01_unit/compiler/sequential_if_return_spec.spl` (8/8 PASS).
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

## Root cause (verified 2026-05-19)

**Hypothesis was speculative; actual fix is confirmed correct in the current tree.**

The bug was a `Control::Return` propagation failure somewhere in the statement-list
executor or `exec_if`. The relevant code paths in the current tree are both correct:

### `exec_if` — `src/compiler_rust/compiler/src/interpreter_control.rs:110`

Each branch uses a bare `return exec_block(...)`, so whatever `Control` the branch
body emits (including `Control::Return(v)`) is forwarded to the caller without
being consumed or swallowed:

```rust
if decision_result {
    return exec_block(&if_stmt.then_block, ...);  // line ~150
}
// elif and else branches follow the same pattern
```

### `exec_block` — `src/compiler_rust/compiler/src/interpreter/block_exec.rs:38`

The statement-list loop explicitly matches non-`Next` control signals and aborts
iteration immediately, propagating them up:

```rust
for stmt in &block.statements {
    match exec_node(stmt, ...) ? {
        Control::Next => {}
        flow @ (Control::Return(_) | Control::Break(..) | Control::Continue(_)) => {
            // run tail injections, then…
            return Ok(flow);   // line ~47 — stops the for loop
        }
    }
}
```

This means: if `if x == 1: return 10` evaluates with condition false and emits
`Control::Next`, the loop advances to the next `if` statement as expected. If the
condition is true and the then-block emits `Control::Return(10)`, `exec_block`
returns it immediately and subsequent `if` statements never execute.

The original hypothesis (statement-list consuming return only once, or the parser
merging sequential `if`s into an `if-elif` chain) is not what the current code
does. The fix commit is not identifiable from git log (file was reorganised into
`interpreter/` subdirectory in commit `d42a48f61e`); the pre-reorganisation code
already shows the same `return exec_block(...)` pattern in the deleted lines.
The regression spec at `test/01_unit/compiler/sequential_if_return_spec.spl` (8 cases,
i64 and u8 variants) is the guard against future regressions.

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

Regression spec exists at `test/01_unit/compiler/sequential_if_return_spec.spl`
(8 cases: i64 classify + u8 classify_u8, both first/second/third branch and
default fallthrough). The doc records 8/8 PASS as of 2026-05-03.

**Note:** the spec could not be re-run from the investigation sandbox (binary
exits code 3 in sandboxed ctx_execute). The control-flow code path was verified
by direct code inspection (see Root cause section above) — the mechanism is
correct in the current tree.

## Cross-references

- `feedback_simple_parser_strict_callsites.md`
- W18-K SCRAM-SHA-256 commit (search session log for "SCRAM" + "elif")
- Bug `it_block_var_mutation_lost_2026-05-01.md` — related interpreter
  control-flow corruption pattern
