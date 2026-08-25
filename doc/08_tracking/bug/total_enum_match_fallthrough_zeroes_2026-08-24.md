# A TOTAL enum match falls through to `const 0` instead of trapping (2026-08-24)

**Status: FIXED (pure-Simple MIR lowering). Rust-seed HIR lowering gap REPORTED, not fixed.**

## Defect

`lower_enum_match` (`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`)
lowers `match e: case A: ... case B: ...` to an if-chain of
`rt_enum_discriminant(e) == disc`. With no `case _:` default arm the last
`next_block` simply `goto`s `merge_block`, and merge emits
`emit_const(result, MirConstValue.Int(0), MirType.i64())`. A match that fires
**no arm** therefore takes no branch, yields `0`, and says nothing.

When the match is **total** — every variant of the enum is named — that
fall-through is not "the programmer forgot a variant". It is the scrutinee not
being a value of that enum at all: a mis-bound receiver, a corrupt tag, or a
bare-name enum collision. The `0` then flows onward as a valid-looking pointer.

## Why it matters

Found while diagnosing the self-hosting blocker
(`stage3_n_modules_zero_segv_mir_lowering_x86_64_2026-08-24.md`). `.unwrap()` on
an erased optional receiver was mis-bound to the async `Poll<T>.unwrap`, which
matches `Poll::Ready` / `Poll::Pending` — a total two-case match. The value
matched neither tag, fell through, and returned `0`, producing a "Some with a
zeroed payload". The lane that found it wrote: *"Had it trapped this was a
one-hour bug"* — instead it cost a full day and many lane-cycles.

## Backend survey (2026-08-24, at `d7a667bb37e`)

| tier | behaviour on no-arm-matched |
|---|---|
| pure-Simple MIR lowering -> LLVM / cranelift / C / wasm / isel | **`const 0`, silent** (this defect) |
| pure-Simple AST interpreter (`10.frontend/core/interpreter/eval.spl:913-917`) | `report_match_fallthrough` + hard stop under safety profile — already correct |
| pure-Simple MIR interpreter (`95.interp/mir_interpreter.spl:1375`) | handles `Unreachable`, but match never produced one |
| Rust seed, tree-walk, match **expression** (`interpreter/expr/control.rs:332+`) | semantic error — correct |
| Rust seed, tree-walk, match **statement** (`interpreter_control.rs:4952`) | `Ok((Control::Next, None))` — silent fall-through |
| Rust seed, HIR lowering (`hir/lower/expr/control.rs:464`, `stmt_lowering.rs:2107`) | `HirExprKind::Nil` tail -> `ConstInt 0/3` — silent |

Exactly the shape the task warned about: a defect present in one tier while
others were correct.

## Fix

One edit, at the single choke point every native backend inherits:
`lower_enum_match`, inside the existing `if not has_default:` branch. When the
match is total, emit `rt_panic(msg)` followed by `MirTerminator.Abort` on the
fall-through block instead of letting it reach the placeholder.

Two halves, the same shape `lower_bootstrap_panic_call` already documents: the
call makes the message survive; the `Abort` makes the block **diverge**, so
control cannot run on even if `rt_panic` is stubbed or returns.

**No new MIR opcode.** `MirTerminator.Abort` was already declared and already
handled by every backend (LLVM text/lib, C, wasm, lua, cuda, vulkan, opencl,
x86_64/aarch64/riscv isel). `rt_panic` is defined in **both** runtime mirrors —
`src/runtime/runtime_native.c:11870` and
`src/compiler_rust/runtime/src/value/sffi/contracts.rs:11` — so this is not a
repeat of the `rt_unwrap_or_trap` NULL-GOT incident.

### The four gates (blast-radius control)

The trap fires only when **all** hold. Each removes a way a *valid* value could
reach the fall-through:

1. `missing_v.len() == 0` and `enum_discs.len() > 0` — the arms name every
   variant. Non-exhaustive matches keep the placeholder-0 behaviour, so the
   **286 in-tree non-exhaustive sites** that the existing warn-only choice was
   measured against are untouched.
2. `self.enum_variant_index.has(enum_name)` — otherwise "no missing variants" is
   vacuously true.
3. `not self.enum_bare_name_collisions.has(enum_name)` — with a contested bare
   name the index may be a *different* enum's (possibly shorter) variant list.
   This is precisely the soundness gap the existing warn-only TODO cites as its
   reason for deferring a compile-time promotion.
4. `all_discs_resolved` (every entry of `enum_discs` `>= 0`) and `not any_guarded`
   (no arm carries `has_guard`) — an arm left at the `-1` sentinel never matches
   a real value, and `case V(x) if cond:` covers `V` textually but does not fire
   when the guard is false. Either would make a name-exhaustive match fall
   through on a perfectly good scrutinee.

This is a **runtime** trap on provably-unreachable code, deliberately *not* the
compile-time promotion the existing TODO defers. The TODO's soundness objection
("unsound in both directions") applies to a static hard error; it does not apply
here, because this fires only if execution actually arrives.

## Verification — mutation-tested both directions

Fixture (`extern fn rt_enum_new(enum_id, discriminant, payload)` builds a value
whose tag matches no variant — the corrupt-tag case):

```
enum Signal:
    Ready
    Pending
fn classify(s: Signal) -> i64:
    match s:
        case Signal.Ready: return 10
        case Signal.Pending: return 20
fn main():
    print("good=" + classify(Signal.Ready).to_text())
    print("bogus=" + classify(rt_enum_new(4242, 99, 0)).to_text())
    print("SURVIVED-FALLTHROUGH")
```

Real `native-build` + execution (not a source scan), seed rebuilt from this tree:

**Pre-fix** (source reverted, rebuilt, re-run) — `BUILD_RC=0`, `RUN_RC=0`:
```
good=10bogus=0SURVIVED-FALLTHROUGH
```

**Post-fix** — `BUILD_RC=0`, `RUN_RC=1`:
```
PANIC: total enum match fell through on 'Signal': the value's discriminant matched NONE of the arms (Ready, Pending), which cover every variant of that enum. The
[crash] report written to /tmp/simple_crash_1009952.log
good=10
```

`good=10` still prints in both: the valid path is unaffected. `bogus=0` and
`SURVIVED-FALLTHROUGH` are gone.

## Gate

`scripts/check/check-total-enum-match-traps.shs` — `--selftest` first and fatal
(5 fixtures: clean, pre-fix, gate-removed, disarmed-but-tokens-present, missing
file), verdict last, `PASS n>0` / `FAIL` 1 / `ERROR` 2, 0 checks is ERROR.
Source half always runs. Build half opt-in (`SIMPLE_MATCH_TRAP_BUILD=1`) does a
real `native-build` + run under `timeout`, with **rc=124 classified as a distinct
HANG failure**, an exit-0 fixture as FAIL ("fall-through did NOT trap"), and a
trap that does not name the enum as FAIL. Exit codes are read directly into a
variable on the line after each invocation, never through a pipe.

Measured:
```
PASS — 3 check(s) performed, total-enum-match trap intact at src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl; build half: fixture trapped rc=1 naming 'TrapProbe'
```
Reverting the source edit alone turns it red:
```
FAIL — 1 check(s) performed, offender(s): source-half(missing: total_match_trap_ok all_discs_resolved any_guarded terminate_abort-call)
```

## Blast radius, measured (2026-08-25)

Headline: **no legitimate program hit the trap.** `grep -c "total enum match
fell through"` over every run log of every natively-built-and-executed program
in this sweep returns **0**. The only place the trap has ever fired is the
fixture built to force it.

Method: native-build + run each program with the fixed compiler, then repeat the
failures against a **pre-fix control worktree** (`HEAD~1`, verified to contain
zero occurrences of `total_match_trap_ok`) using the same seed binary. Reverting
in place was deliberately avoided — the compiler `.spl` source is read live on
every run, so an in-tree revert would have corrupted the concurrently running
jobs.

| program | post-fix | pre-fix control | verdict |
|---|---|---|---|
| `test/perf/bytes_push_1mib.spl` | run rc=0 | — | OK |
| `test/04_smoke/compiler_unparenthesized_tuple_for_runtime.spl` | build rc=0, run **rc=139** | build rc=0, run **rc=139** | **PRE-EXISTING** |
| `test/04_smoke/compiler_unparenthesized_tuple_for.spl` | build **rc=1** | build **rc=1** | **PRE-EXISTING** |
| `test/perf/run_duplicate_check.spl` | build **rc=1** | — (fails in HIR, upstream of this change) | **PRE-EXISTING** |

Attribution detail, so none of this rests on inference:

- **The SEGV is provably untouched.** Beyond the identical `rc=139` on both
  sides, `sha256sum` of the post-fix and pre-fix binaries for
  `compiler_unparenthesized_tuple_for_runtime.spl` collapses to **one distinct
  hash** — the two executables are **byte-identical**, so this change cannot
  have contributed to the crash. Its run log also shows a bare
  `[simple-runtime] Fatal: SIGSEGV`, with no `rt_panic` line and no
  `total enum match fell through` text, which is independently inconsistent with
  the trap having fired.
- **Both build failures are missing-name defects, not codegen.**
  `compiler_unparenthesized_tuple_for.spl` fails with
  `error: MIR lowering error: unresolved method call: enumerate` — verbatim
  identical on the pre-fix control — and the file does call `.enumerate()`
  (`names.enumerate()`, line 6). `run_duplicate_check.spl` fails earlier still,
  in **HIR** lowering (`unresolved name: exit`, `default_config`,
  `collect_files`), a phase upstream of the MIR site this change touches.

**Inconclusive by design, reported rather than omitted:** a whole-compiler blast
build (`native-build src/app/cli/bootstrap_main.spl`, 694 modules) was started
and killed by this lane. It was not a red — it never reached a verdict. Running
the pure-Simple compiler under the seed *interpreter* parsed only 122/694 modules
in 547 s, projecting well past its 3600 s cap before MIR lowering even began; it
was stopped to free capacity for the control run, which is the decisive evidence.
That measurement needs a deployed native compiler to be affordable and is left
open rather than claimed.

**Two structural reasons the blast surface is small**, stated so the low count is
not mistaken for a thin sample: the trap exists only in *natively generated*
code, so every interpreted path (which is most of the test suite) is unaffected
by construction; and within native code the four gates confine it to matches
that are total, name-unambiguous, fully resolved and unguarded — i.e. code no
valid value can reach.

## Known gaps, stated rather than papered over

- **The Rust seed is not fixed.** `hir/lower/expr/control.rs:464` and
  `stmt_lowering.rs:2107` still lower the no-arm tail to `Nil`, and
  `interpreter_control.rs:4952` still returns `Control::Next`. The seed is
  bootstrap-only and its compiled output is not what shipped the incident, so
  expanding the change there was deliberately declined rather than forgotten.
- The trap message survives on backends that carry it (C `spl_panic`, and the
  `rt_panic` call on every native backend). Backends that lower `Abort` to a bare
  INT3/BRK/EBREAK still stop hard, but the message comes from the `rt_panic`
  call that precedes it, not from the terminator.
- `-fsyntax-only`-style static proof is not claimed: the evidence above is a
  built-and-executed binary.
