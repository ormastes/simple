# WASM WAT codegen matched the MirOperand STRUCT against non-existent variants — every call and every operand silently dropped

**Date:** 2026-08-01
**Status:** FIXED — all four defects **executed and verified** against a
before/after control with the canonical LLVM bootstrap binary. See
"Verification". (The original filing said UNCOMPILED; that no longer applies.)

**Generalizable lesson:** an unknown identifier in `case` position is not a
compile error and not merely a dead arm — it is parsed as an **irrefutable
binding pattern**, so it silently swallows every variant below it and makes the
remaining arms, including `case _:`, unreachable. One misspelled arm name
disabled four constant kinds here with no diagnostic at any layer.
**Severity:** Silent wrong-code. No diagnostic, no error, no warning.
**Component:** `src/compiler/70.backend/backend/wasm/wat_codegen.spl`
**Sibling filed in the same sweep:** `isel_mirconstvalue_str_undefined_symbol_2026-08-01.md`

## Ground truth

`src/compiler/50.mir/mir_instruction_support.spl:216`

```
enum MirOperandKind:
    Copy(local: LocalId)
    Move(local: LocalId)
    Const(value: MirConstValue, type_: MirType)
```

`MirOperand` is a **struct** with a single field `kind: MirOperandKind`.
There is no `Use` variant and no `Constant` variant anywhere in the enum.

## Defect 1 — `translate_call` (was line 477)

```
match func_op:                      # <- the STRUCT, not .kind
    case Constant(name):            # <- not a variant
        builder.emit("call ${name}")
    case Use(local_id):             # <- not a variant
        builder.emit_local_named_get("_l{local_id.id}")
        builder.emit("call_indirect")
                                    # <- and NO `case _:`
```

Two errors compound:

1. The scrutinee is the `MirOperand` struct rather than `func_op.kind`.
2. Both arm names (`Constant`, `Use`) are not `MirOperandKind` variants.

With no `case _:` default, the match falls through for **every** real callee.
`translate_call` therefore emits the argument pushes, emits **no call
instruction at all**, and then runs `emit_local_named_set` on the destination —
consuming whatever the last argument push left on the value stack as if it were
the call's return value. Every WASM call is silently replaced by "store the last
argument into the result local". No diagnostic is produced.

## Defect 2 — `emit_operand` (was line 520) — same file, same shape, wider blast radius

```
match operand:                      # <- the STRUCT, not .kind
    case Use(local_id): ...         # <- not a variant
    case Constant(value): ...       # <- not a variant
    case Move(local_id): ...        # real variant name, but the scrutinee is
                                    #    the struct, so it never matches either
    case _:
        builder.emit(";; unhandled operand")
```

Because the scrutinee is the struct, even the correctly-named `Move` arm never
fires. **Every** operand falls to the default, which emits a WAT *comment* —
pushing **nothing** onto the WASM value stack.

This is the more damaging of the two. `emit_operand` is the universal push
helper: `translate_binop` calls it twice before emitting `i64.add`,
`translate_call` calls it per argument, `translate_terminator` calls it for
`Ret`/`CondBranch`. Every one of those consumers assumes a push happened. A
short value stack does not fail loudly — it mis-binds, so each instruction
consumes whatever an *unrelated* earlier instruction left behind.

Net effect: the WASM/WAT backend emits comments where it should emit code, for
every operand and every call, with zero diagnostics.

## Defect 3 (sibling, same family) — `is_self_call`, `src/compiler/60.mir_opt/mir_opt/tco.spl:127`

```
match func_op.kind:
    case Constant(val_):            # <- not a MirOperandKind variant
        match val_:
            case FunctionRef(name): # <- not a MirConstValue variant either
                name == func_name
            case _: false
    case _: false
```

Here the scrutinee is correct (`.kind`), but both variant names are invented.
Both matches fall through to `false`, so `is_self_call` **always** returns
false and tail-call optimization has been silently dead for every function in
the tree. The failure mode is a missing optimization plus stack growth on deep
self-recursion that should have been converted to a loop.

## Why this class is not caught

- A `case` arm is not evidence the arm ever runs.
- A match whose arms all miss produces no compile error and no runtime error;
  it just does nothing.
- The `;; unhandled operand` / `;; unhandled unaryop` comments are emitted into
  the WAT output, not to stderr, so nothing surfaces in a build log.

## Fix

Match `.kind`, use the real variant names, and destructure the constant payload
in a **second, top-level match** rather than as a nested sub-pattern — a nested
enum sub-pattern in a payload position always matches and never binds on the
native/JIT lanes (see
`.claude/memory/reference_enum_payload_subpattern_always_matches.md`).

Following the precedent set by `4c140b35e1d` (C backend GPU dim intrinsics) and
`_CBackendTranslate/class_core.spl:80` `emit_unsupported_panic`: unsupported
cases get an explicit failing lowering, **not** a plausible value. For WAT the
analogue of `spl_panic` is the `unreachable` opcode, emitted after an
`;; UNSUPPORTED: ...` marker comment so the reason survives into the output.

Constant operands now get real pushes (`i32.const` / `i64.const` /
`f64.const`, and `i32.const <offset>` for strings via `self.memory.add_string`)
instead of a comment. Aggregate constants (Array/Tuple/Struct/Zero) trap,
because silently pushing nothing is what caused the mis-binding in the first
place.

## Verification

The original filing was **UNCOMPILED**. That is now superseded: with the
canonical 154MB LLVM bootstrap binary at
`src/compiler_rust/target/bootstrap/simple`, all four defects were **executed
and measured**, with a before/after control.

`simple test <spec>` still cannot be used — it times out during whole-tree
module loading before reaching the spec, and never reports on it. Instead a
small driver calls `MirToWat.translate_const` / `emit_operand` /
`translate_call` directly and prints the emitted WAT between markers. Both runs
exited 0, so these are real outputs, not harness failures.

**Control (pre-fix source, restored from git HEAD):**

```
ZERO_I64>>><<<                       # nothing. local unwritten.
ZERO_I32>>><<<                       # nothing.
ARRAY>>><<<                          # nothing -- proves `case _:` unreachable
OPCONST>>>;; unhandled operand<<<    # a comment, pushes nothing
CALL>>>local.set $_l6<<<             # NO `call` instruction at all
```

**After fix (same driver, same binary):**

```
ZERO_I64>>>i64.const 0
local.set $_l0<<<
ZERO_I32>>>i32.const 0
local.set $_l1<<<
ARRAY>>>;; UNSUPPORTED: aggregate constant initializer
unreachable<<<
OPCONST>>>i64.const 7<<<
CALL>>>call $my_func
local.set $_l6<<<
```

Every claim in this document is confirmed by that pair: the zero-init locals go
from unwritten to correctly written at the right width, aggregate constants go
from silently empty to an explicit trap, operands go from a comment to a real
push, and the call instruction appears where previously there was none.

**Caveat on the spec:** `test/01_unit/compiler/backend/wasm_mir_to_wat_spec.spl`
asserts exactly these strings and was written against this verified behaviour,
but could not itself be *run* — `simple test` times out loading the tree before
reaching any spec file. The assertions are transcribed from the measured
driver output above rather than from a green suite run.

## Defect 4 — `translate_const`, same file (fixed in the follow-up change)

`MirConstValue` (`src/compiler/50.mir/mir_types.spl:65`) is
`Int / Float / Bool / Str / Array / Tuple / Struct / Zero`.

`translate_const` matched it correctly (the value *is* the enum here, not a
struct wrapper — so this one is a pure arm-naming defect, not the compound
error), but against a variant set that does not line up:

```
case Unit:                  # <- not a MirConstValue variant. Dead.
    ()
case Nil:                   # <- not a MirConstValue variant. Dead.
    builder.emit("i32.const 0")
    builder.emit_local_named_set("_l{dest.id}")
...
case _:
    builder.emit(";; unhandled constant type")     # <- no local.set
```

**Corrected by execution — it is worse than "Zero falls to `case _:`".**
Running the real translator (transcript below) shows `Zero` and `Array` both
emit **absolutely nothing** — not even the `;; unhandled constant type` comment
from `case _:`. That comment never appears, which proves `case _:` was
*unreachable*.

The mechanism: `Unit` is not a known variant, so a bare unknown identifier in
pattern position is parsed as an **irrefutable binding pattern** — a catch-all,
like `case x:`. It therefore matched *every* constant that got past the four
real arms above it, and its body is `()`, which emits nothing. `Nil`, `Array`,
`Struct` and `case _:` were all dead code behind it.

So a misspelled arm here is not merely dead — it **silently swallows every
remaining variant**. `Zero`, `Tuple`, `Array` and `Struct` constants each
produced zero WAT and left the destination local unwritten, so every later read
of that local observes WASM's implicit zero or a stale value from an earlier
write rather than a value this instruction produced.

This also means the two malformed-interpolation arms below were never reached,
which is the only reason their invalid WAT never surfaced.

Two further wrong-code arms in the same function, found while fixing it:

- `case Array(elements)` emitted `i64.const {elem}` where `elem` is a
  `MirConstValue`, not an integer — interpolating an enum into a numeric WAT
  operand. The emitted text is not a valid `i64.const` argument.
- `case Struct(fields)` iterated a `Dict<text, MirConstValue>`, so `field`
  binds the **key** (a `text`), and emitted `i64.const {field}` — a string
  interpolated into a numeric operand.

Neither had ever been exercised (see "Spec coverage" below). Both now trap
rather than emit malformed WAT.

## Spec coverage — the earlier "no coverage at all" claim is WRONG, and the truth is worse

Measured repo-wide (excluding `.claude/worktrees/`):

- `MirToWat` appears in **zero** spec files. `/usr/bin/grep -rn "MirToWat"
  --include=*_spec.spl .` returns nothing.
- WASM specs *do* exist and are substantial:
  `test/01_unit/compiler/wasm_codegen_spec.spl` (251 lines, 34 `it` blocks),
  `test/01_unit/compiler/backend/wasm_codegen_spec.spl` (86 lines).

So the backend is not untested — but every one of those tests drives
`WatBuilder`, `WasmType`, `WasmTypeMapper` and `wasm_backend` **primitives
directly**. Not one of them constructs a `MirToWat` or feeds it a MIR
instruction. The entire MIR→WAT *translation* layer — `translate_instruction`,
`translate_const`, `translate_call`, `translate_binop`, `emit_operand`, where
all four defects live — has no test at all.

The existing spec file's own header reads:

```
# Validates MIR to WAT translation, control flow structuring, ...
```

It validates none of that. The docstring asserts precisely the coverage that is
missing, which is why four defects survived in a file that *looks* well
covered. A coverage claim in prose is not coverage; only a test that constructs
the unit under test is.

**Added:** `test/01_unit/compiler/backend/wasm_mir_to_wat_spec.spl` — the first
spec that instantiates `MirToWat` and asserts on emitted WAT text. It pins that
a const, a call, and an operand each emit a real instruction, and that
unsupported constants trap instead of emitting a plausible value. Each `it`
block fails against the pre-fix code.

---

# Follow-up 2026-08-01 (second pass): `translate_binop` / `translate_unaryop`

The first pass fixed const/call/operand. Two more functions in the same file
were still carrying the bare-identifier defect
(`case_bare_ident_is_irrefutable_binding_2026-08-01.md`), and the reported
symptom for them was **wrong**.

## The reported symptom was wrong; measurement found the real one

It was reported as "13 float-op victims — everything from `FAdd` onward emits
`f64.add`". Executed against the real enum, the swallowing arm is **`case And:`
at line 414, seven arms earlier than `FAdd`**, and the swallowed instruction is
**`i32.and`**, not `f64.add`.

`MirBinOp` (`mir_instruction_support.spl:178`) has exactly 24 variants:
`Add Sub Mul Div Rem Pow MatMul BitAnd BitOr BitXor Shl Shr Eq Ne Lt Le Gt Ge
BroadcastAdd BroadcastSub BroadcastMul BroadcastDiv BroadcastPow Offset`.

There are **no `And`/`Or`/`Xor`/`Mod` variants and no `F*` float variants at
all**. The ten `f64.*` arms were never lowering anything — they matched a
variant that does not exist. Fixing their spelling would have been meaningless;
the fix is to delete the fiction and restore the arms it was hiding.

## Measured, before → after (bootstrap binary, 24 binops + 4 unaryops)

| op | before | after |
|---|---|---|
| Pow | `i32.and` | `;; UNSUPPORTED` + `unreachable` |
| MatMul | `i32.and` | `;; UNSUPPORTED` + `unreachable` |
| BitAnd | `i32.and` | `i64.and` |
| BitOr | `i32.and` | `i64.or` |
| BitXor | `i32.and` | `i64.xor` |
| Shl | `i32.and` | `i64.shl` |
| Shr | `i32.and` | `i64.shr_s` |
| BroadcastAdd/Sub/Mul/Div/Pow | `i32.and` | `;; UNSUPPORTED` + `unreachable` |
| Offset | `i32.and` | `i64.add` |
| UnaryOp BitNot | `f64.neg` | `i64.const -1` + `i64.xor` |
| UnaryOp Transpose | `f64.neg` | `;; UNSUPPORTED` + `unreachable` |

14 of 24 binops and 2 of 4 unaryops were wrong. Seven of them (`BitAnd`,
`BitOr`, `BitXor`, `Shl`, `Shr`, and unary `BitNot`, plus `Pow`'s body) had a
**correct lowering written directly below the swallowing arm that never ran**.
`case _:` was dead in both functions, so nothing ever reported a problem.

`Offset` follows the in-file `GetElementPtr` lowering (unscaled `i64.add`),
matching the LLVM backend's `getelementptr i8`
(`_MirToLlvm/core_codegen.spl:1261`). `Pow` additionally re-pushed both
operands that were already on the value stack and then emitted only a comment —
four values left on the stack, no result. `wasm_runtime.spl` imports no pow
helper, so it now traps.

## ~~OPEN~~ FIXED in the third pass — see "Follow-up 3" below

`MirBinOp` carries no operand type and `translate_binop` receives none, so a
**float** add/sub/mul/div/comparison still lowers to the `i64.*` instruction —
silently wrong code for any f32/f64 program. This is a missing feature (thread
per-local types from `func.body.locals` into the binop lowering), not the
irrefutable-binding defect, and it is why the fictional `F*` arms looked
plausible enough to survive. It must be fixed before this backend can compile
float arithmetic.

## Spec

`test/01_unit/compiler/backend/wasm_mir_to_wat_spec.spl` grew from 10 to 24
`it` blocks with `translate_binop` and `translate_unaryop` sections. Sabotage
check: re-inserting `case And: builder.emit("i32.and")` above the restored arms
turns the new blocks red.

---

# Follow-up 3 2026-08-01 (third pass): float arithmetic, and the seam it needed

Fixes the OPEN item above. Status: **FIXED, executed and measured** against a
before/after control with `src/compiler_rust/target/bootstrap/simple`.

## The suggested seam did not exist

The OPEN note said to "thread per-local types from `func.body.locals`".
**`MirFunction` has no `body` field.** It carries `locals: [MirLocal]` and
`blocks: [MirBlock]` directly (`mir_instruction_graph.spl:26`), and `MirBody`
is a separate struct built on demand by `MirBody.from_function`. Nor does
`MirFunction` have an `is_extern` field. Measured, not inferred:

```
error: semantic: undefined field: unknown property or method 'body' on Tuple
```

...which also exposes a second thing: `module.functions` is a
`Dict<SymbolId, MirFunction>`, so `for func in module.functions:` bound a
**(key, value) tuple**, not a function. `translate_module` had therefore
**never run to completion even once**. Behind it sat a third defect —
`translate_terminator` did `match term.kind:` but `MirTerminator` is an ENUM,
not a struct with a `.kind` field (the exact mirror of the original
`emit_operand` defect), and its `CondBranch` arm named a variant that does not
exist (the real one is `If`).

That is why a missing operand type went unnoticed for so long: nothing
downstream of `translate_module` was reachable, so no end-to-end output existed
to be wrong.

The real seam is `func.locals`, each `MirLocal` carrying `type_: MirType`
(`mir_types.spl:38` — the field is `type_`, not `ty`, and `name` is `text?`).

## Fix

- `MirToWat.local_types: Dict<i64, text>` maps LocalId → WAT op class
  (`i32`/`i64`/`f32`/`f64`), rebuilt per function by `register_local_types`
  (cleared each time — a stale entry would silently type an unrelated local).
- A `Const` operand is self-describing (`MirOperandKind.Const` carries its own
  `MirType`), so it needs no registration. `Copy`/`Move` resolve through the map.
- `wat_op_class` is deliberately **strict**: it returns `""` for anything with
  no scalar WAT arithmetic form. It does NOT reuse `mir_type_to_wasm_type`,
  whose `case _: WasmType.I32` fallback is fine for declaring a local slot but
  would turn "unknown type" into "emit the integer op" — the very defect here.
- **Unknown, or mismatched left/right, ⇒ `;; UNSUPPORTED:` + `unreachable`.**
  Never a plausible integer op.
- `translate_unaryop` got the same treatment: `Neg` on a float is `f64.neg`,
  not `i64.const 0; x; i64.sub`.
- `translate_function` / `collect_strings` / `translate_module` /
  `translate_terminator` corrected to the real field and variant names, since
  the type map can only be populated on a path that actually runs. Params are
  now named `$_lN` to match the `_l{id}` naming every instruction lowering
  already uses — naming them from `MirLocal.name` produced parameters no body
  instruction could resolve.

## Measured, before → after (same binary, live integer control in both runs)

Control (`i64 Add` → `i64.add`, `i64 Lt` → `i64.lt_s`) is unchanged in both
runs, so these are real deltas, not harness noise. Both runs exited 0.

| operands / op | before | after |
|---|---|---|
| f64 Add / Sub / Mul | `i64.add` / `i64.sub` / `i64.mul` | `f64.add` / `f64.sub` / `f64.mul` |
| f64 Div | `i64.div_s` | `f64.div` |
| f64 Eq / Ne | `i64.eq` / `i64.ne` | `f64.eq` / `f64.ne` |
| f64 Lt / Le / Gt / Ge | `i64.lt_s` / `le_s` / `gt_s` / `ge_s` | `f64.lt` / `le` / `gt` / `ge` |
| f32 Mul | `i64.mul` | `f32.mul` |
| f64 Rem | `i64.rem_s` | `;; UNSUPPORTED` + `unreachable` |
| f64 BitAnd/BitOr/BitXor/Shl/Shr | `i64.and` etc. | `;; UNSUPPORTED` + `unreachable` |
| **i32 Add** | `i64.add` | `i32.add` |
| unregistered local | `i64.add` | `;; UNSUPPORTED` + `unreachable` |
| mismatched f64/i64 | `i64.add` | `;; UNSUPPORTED` + `unreachable` |
| Unit-typed operands | `i64.add` | `;; UNSUPPORTED` + `unreachable` |
| unary Neg on f64 | `i64.const 0; …; i64.sub` | `f64.neg` |
| unary BitNot on f64 | `i64.const -1; i64.xor` | `;; UNSUPPORTED` + `unreachable` |
| `translate_module` (any function) | **aborted**: `'body' on Tuple` | completes |

**The reported symptom was again narrower than the defect.** It was filed as a
float problem; `i32` operands were equally wrong (`i32.const 1; i32.const 2;
i64.add` — not merely a wrong result but invalid WAT, since `i64.add` cannot
consume two i32 stack values).

End-to-end, an f64 function now produces:

```
(func $fmul (param $_l0 f64) (param $_l1 f64) (result f64)
  (local $_l2 f64)
  ... f64.mul
```

Before, `translate_module` aborted before emitting anything.

## Spec: 24 → 46 `it` blocks, and the "24 passing" claim was never observed

`test/01_unit/compiler/backend/wasm_mir_to_wat_spec.spl`. Final:
**`Results: 46 total, 46 passed, 0 failed`**, exit 0.

Sabotage proof (requirement: prove it CAN fail). Forcing the pre-fix behaviour
with a one-line `var cls = "i64"` in `translate_binop` gives
**`Results: 46 total, 32 passed, 14 failed`, exit 1** — every float block, the
i32 block, both unknown-type blocks and the end-to-end `f64.mul` block go red,
while the integer control blocks stay green. Restoring returns 46/46.

A *weaker* sabotage was tried first and rejected: routing floats through
`emit_int_binop` still passed `f64 Add`, because that function interpolates the
class (`"{cls}.add"`) and so coincidentally produced `f64.add`. Only a sabotage
that reproduces the *actual* pre-fix instruction (hardcoded `i64`) is a valid
proof.

## Measurement trap hit during this pass — read before trusting any run here

`simple test <spec>` **does** run this spec, but its output is ~3,600 lines of
lint/deprecation noise with the verdict at line ~3,629. Grepping the head or
tailing 30 lines shows **nothing at all** and the command exits 0, which reads
exactly like "the runner silently executed no tests". It was misread that way
here before `.claude/rules/testing.md` ("capture to a file and read the tail";
"take `$?` from the command under test, never from a pipe") was applied and the
real `Results:` line appeared. The earlier note in this document that
`simple test` "cannot be used, it times out" is **wrong** and is withdrawn.

## Remaining gap — recorded, not silently normalized

**Unsigned integers still lower to signed instructions.** `U8`/`U16`/`U32`
classify as `i32` and `U64` as `i64`, and `emit_int_binop` emits `div_s`,
`rem_s`, `lt_s`, `le_s`, `gt_s`, `ge_s`, `shr_s` unconditionally. For an
unsigned operand these should be `div_u`/`rem_u`/`lt_u`/`le_u`/`gt_u`/`ge_u`/
`shr_u`. Same defect family (instruction not matched to operand type), out of
scope for this float-focused pass, and left explicitly rather than normalized.

Also still stubbed, unchanged by this pass: `Goto` and `If` terminators emit
comments rather than real branches, and `Switch` interpolates `SwitchCase`
structs into a `br_table` operand list. The control-flow lowering in this
backend is not yet real.

## Sibling defect found while verifying — filed separately

`doc/08_tracking/bug/chained_static_ctor_receiver_drops_mutation_2026-08-01.md`
— `MirToWat.create("m").emit_operand(b, op)` emits **nothing**, while the same
call through a plain function or a bound `val` works. This produced 3 phantom
failures in the verification driver and is a false-green generator for any spec
written in the `Class.create(...).method(...)` style.
