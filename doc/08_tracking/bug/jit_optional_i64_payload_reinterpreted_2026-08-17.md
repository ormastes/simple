# JIT: `i64?` optional payloads are reinterpreted as f64 and `!` unwrap always yields nil

- **Date:** 2026-08-17
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Status:** OPEN
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
