# JIT: `i64?` optional payloads are reinterpreted as f64 and `!` unwrap always yields nil

- **Date:** 2026-08-17
- **Status:** FIXED 2026-08-31 (see "Root cause and fix" below). The
  explicit-`return` half was fixed 2026-08-17; the implicit tail-expression
  half stayed broken until 2026-08-31, which is why this record previously
  carried contradictory FIXED/OPEN lines.
- **Severity:** HIGH — silent wrong values, no error, on the engine ordinary
  programs actually run on. No spec in the suite can observe it.
- **Area:** Cranelift JIT (`bin/simple run` default path)
- **Found by:** old-bug-backlog audit, while trying to verify the closure of
  `interpreter_bang_unwrap_member_access_2026-05-08.md`

## Symptom

Every operation on an `i64?` optional is corrupt under the JIT. Measured with
`bin/simple run` (binary `bin/release/x86_64-unknown-linux-gnu/simple`,
59,536,728 bytes, 2026-08-16 22:59):

| expression | interpreter | JIT |
|---|---|---|
| `val x: i64? = 42` then `x.to_string()` | `42` | `0.000…0002` (a denormal f64) |
| `x!` | `42` | `nil` |
| `x ?? 99` | `42` | `0.000…0002` |
| `give_int()` returning `7`, `.to_string()` | `7` | `<value:0x7>` |
| `give_int()!` | `7` | `nil` |

Two distinct corruptions are visible:

1. **Payload reinterpreted as f64.** `0.000…0002` is the decimal rendering of
   the *bit pattern* of the integer 42 read as an IEEE-754 double (42 as f64
   bits is a denormal, ~2.08e-322). The payload is not lost — it is read
   through the wrong type.
2. **Tagged handle leaked to the user.** `<value:0x7>` is the boxed
   representation of `7` printed raw, so the optional returned across a
   function boundary is never unboxed at all.

`!` unwrap then yields `nil` for a plainly non-nil optional, and — worst of the
set — `??` silently returns the corrupt payload instead of taking the default,
so there is no branch a caller could add to detect this.

## Reproduce

```
cat > /tmp/opt.spl <<'EOF'
fn give() -> i64?:
    return 7
fn main():
    val x: i64? = 42
    print("x=" + x.to_string())
    print("bang_x=" + x!.to_string())
    val g = give()
    print("g=" + g.to_string())
    print("bang_g=" + g!.to_string())
    print("coalesce=" + (x ?? 99).to_string())
main()
EOF
bin/simple run /tmp/opt.spl                                  # corrupt
SIMPLE_EXECUTION_MODE=interpreter bin/simple run /tmp/opt.spl  # correct
```

## Why this was never caught

`bin/simple test` hard-defaults to the tree-walk interpreter
(`.claude/rules/testing.md`: "`run` and `test` are DIFFERENT ENGINES";
`TestExecutionMode` has no JIT variant). The interpreter is **correct** on
every case above, so a spec asserting the right values passes and proves
nothing about the JIT. This is a concrete instance of the documented
711-spec blind spot.

It also explains why
`interpreter_bang_unwrap_member_access_2026-05-08.md` was closed as
"FIXED 2026-05-10 -- verified by interpreter repro (all Cases A/B/C pass)".
That verification was real but covered one engine; the parse errors it
described are genuinely gone. The closure is not wrong, it is **partial** —
and its cited spec file no longer exists, so nothing has re-checked it since.

## Coverage added with this report

- `test/01_unit/compiler/interpreter/optional_unwrap_bang_spec.spl` — pins the
  interpreter values (`Results: 5 total, 5 passed, 0 failed`). Sabotage-proved:
  changing one expected value gives `5 total, 4 passed, 1 failed`, and
  reverting restores 5/5.
- `test/01_unit/compiler/interpreter/probe_optional_unwrap_jit.spl` — the run
  -path mirror, the only artifact that can see this defect. **Deliberately RED**
  on the JIT (exit 1, all 5 checks fail) and green on the interpreter (exit 0),
  so it fails closed rather than printing and exiting 0.

Run both with `--no-session-daemon` (see note below).

## Unblock condition

Close this when `bin/simple run
test/01_unit/compiler/interpreter/probe_optional_unwrap_jit.spl` prints
`OPTIONAL_UNWRAP PROBE: ALL PASS` and exits 0 without
`SIMPLE_EXECUTION_MODE=interpreter`.

## Operational note found alongside

`--no-session-daemon` took this spec from ~115 s to **683 ms**, and without it
the run failed outright with `ERROR: test daemon request expired before
execution` under concurrent load. Unrelated to the defect, but it is what makes
verifying it affordable.

## Root cause and fix (2026-08-31)

The remaining half of this bug was the **implicit tail-expression return**.
`HirStmt::Return` (`src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs`)
already applied `box_scalar_for_tagged_slot` / `unbox_scalar_for_raw_slot`, so
`fn f() -> i64?: return 42` was correct. The `HirStmt::Expr` arm — whose value
`lowering_core.rs:2030-2032` turns directly into `Terminator::Return` — applied
neither, so `fn f() -> i64?: 42` returned the RAW word into a tagged return
slot and the caller decoded it through the wrong tag:

| declared return | tail-return value observed pre-fix |
|---|---|
| `i64?` returning `42` | `~2.08e-322` (bits of 42 read as f64) |
| `f64?` returning `2.5` | `576601489791778816` (= bits(2.5) >> 3) |
| `bool?` returning `true` | `nil` |

`??` did not rescue any of them. Fixed by applying the same coercion pair at
the tail-expression site. Probe:
`test/01_unit/compiler/interpreter/probe_optional_tail_return_jit.spl`
(8 FAILURES before, ALL PASS after, on `bin/simple run`).

### Still open, filed separately rather than bundled here

- **`Any?` tail or explicit return still yields `<value:0x7>`.**
  `slot_holds_tagged_value` treats `T?` as `Pointer{inner}` and only accepts it
  when `inner` is a raw scalar, so `Any?` (= `Pointer{ANY}`) is never boxed.
  Plain `Any` is correct. Widening that predicate touches every `Let`/`Assign`/
  argument site, so it was left out of a minimal fix.
- **`if v != nil:` does not narrow `i64?` to `i64`.** The interpreter fails
  closed (`error: semantic: type mismatch: cannot convert enum to int`); the
  JIT accepts the same program and computes `42 << 3 = 336`. Two issues: the
  narrowing itself is a language design decision, and the JIT silently
  diverging from a program the semantic checker rejects is its own defect.
