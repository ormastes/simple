# JIT: `i64?` optional payloads are reinterpreted as f64 and `!` unwrap always yields nil

- **Date:** 2026-08-17
- **Status:** FIXED 2026-08-17 (see "Resolution" below) — provable only on a
  freshly built seed; the deployed `bin/simple` predates the fix.
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

## Resolution (2026-08-17)

One root cause, three lowering sites, all in the Rust seed.

**Root cause.** Every boxing guard in MIR lowering tested `ty == TypeId::ANY`.
A nullable scalar `T?` lowers to `HirType::Pointer { inner: T }` and is equally
a tagged-value slot — it must be able to hold tagged nil — so a raw scalar was
stored into it unboxed and later decoded by its own low 3 bits.

| commit | site | symptom it fixed |
|---|---|---|
| `3bc00fe409c` | `mir/lower/lowering_core.rs` + `lowering_stmt.rs` — new `slot_holds_tagged_value` / `box_scalar_for_tagged_slot`, used at `Let`, local assign, global assign, and `Return` | `x=…denormal`, `g=<value:0x7>` |
| `653dc67cad0` | `hir/lower/expr/control.rs` `lower_try` — `!`/`?` on a nullable scalar no longer routes through `rt_enum_payload`, which answers `rt_core_nil()` for a non-enum | `bang_x=nil`, `bang_g=nil` |
| `4c3202cf575` | `hir/lower/expr/control.rs` `lower_coalesce` — the `??` DEFAULT arm is boxed when it flows out through a tagged slot | `n ?? 9` printed `<invalid-heap:0x9>` (`9 & 7 == 1` is TAG_HEAP) |

**Before / after**, `bin/simple run /tmp/opt.spl` (JIT):

```
BEFORE (bin/release/x86_64-unknown-linux-gnu/simple, 59,536,728 B, 2026-08-16 22:59)
x=0.000…0002   bang_x=nil   g=<value:0x7>   bang_g=nil   coalesce=0.000…0002
AFTER  (freshly built seed, same source tree)
x=42           bang_x=42    g=7             bang_g=7     coalesce=42
```

The report's unblock condition is met: `bin/simple run
test/01_unit/compiler/interpreter/probe_optional_unwrap_jit.spl` prints
`OPTIONAL_UNWRAP PROBE: ALL PASS` and exits 0 without
`SIMPLE_EXECUTION_MODE=interpreter`.

**Provable only after redeploy.** The deployed `bin/simple` is a Rust seed from
2026-08-16 that predates all three commits, so it still reproduces the bug. All
"AFTER" evidence above comes from an isolated incremental rebuild
(`CARGO_TARGET_DIR=/mnt/data/cargo-target-jit-hp cargo build --release --bin
simple`). The specs below take `SIMPLE_BIN` so a lane can point them at a
candidate binary; with `SIMPLE_BIN` unset they measure whatever ships.

### Specs

- `test/01_unit/compiler/codegen/optional_scalar_payload_roundtrip_spec.spl` —
  REPRODUCING spec. Its subprocess example runs the repro under both engines,
  because a spec file falls back to the interpreter (which was always correct),
  so in-process examples can never go red on a JIT defect. Reproduce-first
  evidence: `Results: 5 total, 4 passed, 1 failed` against the pre-fix binary,
  `Results: 5 total, 5 passed, 0 failed` against the rebuilt one.
- `test/01_unit/compiler/codegen/scalar_slot_roundtrip_class_spec.spl` +
  `test/01_unit/compiler/codegen/probe_scalar_slot_roundtrip_jit.spl` —
  SIMILAR-PROBLEM DETECTION for the defect CLASS (see the sibling f32 report):
  i8/i16/i32/i64/u8/u16/u32/u64/f32/f64/bool/text across nullable `T?` (bind,
  return, `!`, `??`, and the nil-default arm), struct fields (construction AND
  assignment paths, plus a neighbour-intact check), and array elements
  (including a struct read out of an array). Pre-fix: `SCALAR_SLOT_ROUNDTRIP
  PROBE: 30 FAILED` (class spec `3 total, 1 passed, 2 failed`). Post-fix: `ALL
  PASS` on BOTH engines (class spec `3 total, 3 passed, 0 failed`).

## Operational note found alongside

`--no-session-daemon` took this spec from ~115 s to **683 ms**, and without it
the run failed outright with `ERROR: test daemon request expired before
execution` under concurrent load. Unrelated to the defect, but it is what makes
verifying it affordable.
