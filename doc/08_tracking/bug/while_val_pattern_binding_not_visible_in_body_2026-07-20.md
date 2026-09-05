# Bug: `while val Pattern(x) = expr:` loop body cannot see `x` (`variable not found`)

- **Date:** 2026-07-20
- **Status:** OPEN — re-reproduced 2026-08-17 by execution (see "Re-verification
  2026-08-17" at the bottom; scope now narrowed to the SSpec `it`-block path only)
- **Status (original):** open (found triaging `test/feature/usage/pattern_matching_advanced_spec.spl`)
- **Area:** `while val`/`while let` pattern-binding scope (interpreter or HIR
  lowering, not isolated further in this pass), deployed seed at
  `bin/release/x86_64-unknown-linux-gnu/simple`

## Symptom

```
✗ loops while pattern matches
  semantic: variable `value` not found
```

The spec originally used `while let Some(value) = next_item(counter):` — per
`.claude/rules/language.md` ("Pattern binding: `if val` not `if let`"), `let`
is not Simple's keyword here, so this pass first corrected the spec to `while
val Some(value) = next_item(counter):`. The error is **identical** either way
— this rules out "wrong keyword" as the (sole) cause and confirms a genuine
binding-scope gap for `while val`/`while let` pattern destructuring
specifically (as opposed to `if val`, which per the same language rule is the
documented/working form and is used successfully elsewhere in this test
cluster, e.g. throughout `safe_unwrap_operators_spec.spl` fixes in this same
pass).

## Minimal repro

```simple
describe "repro":
    it "while val binds pattern var":
        fn next_item(n: i64) -> Option<i64>:
            if n > 0:
                Some(n)
            else:
                None

        var counter = 3
        var sum = 0
        while val Some(value) = next_item(counter):
            sum = sum + value
            counter = counter - 1
        expect sum == 6
```

`bin/release/x86_64-unknown-linux-gnu/simple test <repro>.spl --no-session-daemon`:
```
✗ while val binds pattern var
  semantic: variable `value` not found
```

## Root cause

Not isolated to a specific source location in this pass. The loop condition's
pattern-bound variable (`value`, from `Some(value)`) is evidently not being
registered into the loop body's scope, unlike `if val Pattern(x) = expr:` whose
bound variable IS visible inside the `if` body (used successfully throughout
this repo's specs).

## Fix direction (not applied — compiler-internals change, needs rebuild)

Compare the scope-binding logic for `if val`/`if let` (working) against
`while val`/`while let` (broken) in the parser/HIR-lowering/interpreter and
apply the same binding mechanism to the loop-body scope.

## Verification

Reproduced at repo tip (2026-07-20) via:
```
bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/pattern_matching_advanced_spec.spl --no-session-daemon
bin/release/x86_64-unknown-linux-gnu/simple test <repro spec above> --no-session-daemon
```
Not checked against the pure-Simple self-hosted compiler or a compiled/native
path — only the Rust seed interpreter was probed.

## Re-verification 2026-08-17 — STILL FAILING, scope narrowed

Binary identity:
```
$ readlink -f bin/simple
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
$ stat -c '%s %y' "$(readlink -f bin/simple)"
59537240 2026-08-17 12:58:51.339525019 +0000
```
(`bin/simple --version` still prints the Rust-seed warning banner, so all
evidence below is SEED evidence.)

Repro above, unchanged:
```
$ bin/simple test <repro>.spl --no-session-daemon
  ✗ while val binds pattern var
    semantic: variable `value` not found
1 example, 1 failure
Results: 1 total, 0 passed, 1 failed   (exit 1)
```

**New: the defect is NOT in `while val` generally — it is specific to the
SSpec `it`-block execution path.** The same loop at ordinary function scope
works on BOTH engines:
```
$ bin/simple run wv.spl                                  -> sum=6   (exit 0)
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run wv.spl -> sum=6  (exit 0)
```
(`wv.spl` = the same `next_item` + `while val Some(value) = next_item(counter)`
loop inside `fn main()`.)

And within one spec file, `if val` passes where `while val` fails, with the
helper hoisted to top level so nested-`fn`-in-`it` is ruled out:
```
  ✗ while val binds pattern var (top-level fn)   semantic: variable `value` not found
  ✓ if val binds pattern var
2 examples, 1 failure
```

### Root cause localization (2026-08-17)

The error string is emitted only by the Rust seed's AST tree-walk interpreter
(`src/compiler_rust/compiler/src/interpreter/{expr/literals.rs:379,
node_exec.rs}`), not by any `.spl` source. Two candidate sites were read and
BOTH look correct in isolation, so neither is yet confirmed as the fault:
- `interpreter_control.rs:387-407` (`exec_while`) does handle
  `while_stmt.let_pattern`, inserting `pattern_matches` bindings into `env`
  before `exec_block`.
- `interpreter/expr/control.rs:475-483` (`Node::While` free-variable
  collection for closure capture) does call `bind_pattern_vars` on
  `let_pattern`, symmetrically with the working `Node::If` arm at 443-450.
The remaining suspect is whichever statement executor the `it`-block closure
body actually uses, which evidently is not the `exec_while` path above (that
path demonstrably works under `bin/simple run`).

### Why not fixed in this pass

There is **no `.spl` implementation of this path to fix**: `while val`
statement execution for the `simple test` engine lives entirely in the Rust
seed (`src/compiler_rust/compiler/src/interpreter*`). A fix requires editing
the Rust seed and rebuilding + redeploying `bin/release/<triple>/simple`, which
`.claude/rules/bootstrap.md` explicitly warns against doing ad hoc in this
shared working tree. Left OPEN with the fresh evidence above.

## Re-run 2026-08-17 on the NEWLY REDEPLOYED Rust seed — STILL RED

Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
md5 `669150b61f2f20401a6a895ae54e9fee`, size 59550432, mtime
2026-08-17 20:10:45 UTC.

```
$ timeout 3000 nice -n 19 bin/simple test \
    test/feature/usage/pattern_matching_advanced_spec.spl --no-session-daemon
  ✗ loops while pattern matches
    semantic: variable `value` not found
Results: 20 total, 19 passed, 1 failed
EXIT=1
```

**Verdict: STILL-OPEN.** The single failure is exactly the `while val` example
and the error string is unchanged (`variable \`value\` not found`), so the seed
rebuild did not touch the SSpec `it`-block statement-executor path that this
defect is localized to.
