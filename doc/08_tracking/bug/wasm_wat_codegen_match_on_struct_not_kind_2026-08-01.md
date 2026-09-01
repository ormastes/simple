# WASM WAT codegen matched the MirOperand STRUCT against non-existent variants — every call and every operand silently dropped

**Date:** 2026-08-01
**Status:** FIXED (see "Fix" below). Fix is **UNCOMPILED** — see "Verification".
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

**UNCOMPILED.** The deployed `bin/simple` has no `lint`/`test`/`run`
subcommands (see `.claude/memory/reference_live_bin_simple_lost_all_subcommands_2026-08-01.md`),
and `src/compiler_rust/target/bootstrap/simple lint` on these four files did not
return within the available window. The change is a static correction validated
against the enum definitions quoted above; it has **not** been compiled or
executed.

## Follow-ups not taken in this change

- `translate_const` (same file) has `case Unit:` and `case Nil:` arms —
  neither is a `MirConstValue` variant, so both are dead. The real `Zero`
  variant falls to `case _:` and emits `;; unhandled constant type` with no
  `emit_local_named_set`, leaving the destination local unwritten. Same class,
  left for a separate change to keep this diff scoped.
- The WASM backend appears to have no spec coverage at all; nothing in the
  suite would have caught any of this.
