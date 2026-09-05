# Native ISel called a function that does not exist: `mirconstvalue_Str` — direct calls silently dropped on x86_64 and aarch64

**Date:** 2026-08-01
**Status:** FIXED (see "Fix" below). Fix is **UNCOMPILED** — see "Verification".
**Severity:** Silent wrong-code. No diagnostic, no link error, no warning.
**Component:**
- `src/compiler/70.backend/backend/native/isel_x86_64.spl:347`
- `src/compiler/70.backend/backend/native/isel_aarch64.spl:598`

**Sibling filed in the same sweep:** `wasm_wat_codegen_match_on_struct_not_kind_2026-08-01.md`

## The symbol does not exist

Anchored, tree-wide:

```
$ grep -rn "mirconstvalue_Str" --include=*.spl .
src/compiler/70.backend/backend/native/isel_x86_64.spl:347:        case Const(mirconstvalue_Str(name), _):
src/compiler/70.backend/backend/native/isel_aarch64.spl:598:        case Const(mirconstvalue_Str(name), _):
```

Exactly two occurrences, and **both are use sites**. There is no `fn
mirconstvalue_Str`, no `@extern fn mirconstvalue_Str`, and no import of that
name anywhere in the repository.

## Ground truth

`src/compiler/50.mir/mir_types.spl:65`

```
enum MirConstValue:
    Int(value: i64)
    Float(value: f64)
    Bool(value: bool)
    Str(value: text)
    ...
```

The callee symbol for a direct call is carried in `MirConstValue.Str`. The
correct spelling is `Str`, reached through the `MirConstValue` enum — which is
already imported at the top of both files.

## Mechanism

Both sites are the direct-call arm of the call-lowering match:

```
match func_op.kind:
    case Const(mirconstvalue_Str(name), _):
        current_ctx = isel_add_extern(current_ctx, name)
        insts.push(new_mach_inst(X86_OP_CALL, [op_sym(name)]))   # / A64_OP_BL
    case Copy(local): ... indirect ...
    case Move(local): ... indirect ...
    case _:
        insts.push(new_mach_inst(X86_OP_NOP, []))                # / A64_OP_NOP
```

Every direct call in the program has `func_op.kind == Const(Str(name), _)`. The
undefined nested pattern means that arm never selects, so control reaches the
`case _:` default and the backend emits a **`NOP`** where the `CALL`/`BL` should
be. Immediately after the match both backends unconditionally execute:

```
insts.push(new_mach_inst(X86_OP_MOV_REG_REG, [local_vreg_op(dest.id), op_phys(X86_RAX)]))
```

so the destination local is loaded from `rax` (`x0` on aarch64) — which now
holds a stale value from whatever last wrote that register, because no call
took place. The callee is also never registered via `isel_add_extern`, so it
never reaches the extern symbol table.

Result: on the native x86_64 and aarch64 ISel paths, every direct function call
becomes "no-op, then read garbage out of the return register". No error is
raised at any stage.

## Two separate errors, both needed the fix

1. **The symbol is undefined.** `mirconstvalue_Str` exists nowhere.
2. **The nested-pattern shape is wrong regardless of spelling.** Even written
   correctly as `case Const(MirConstValue.Str(name), _)`, a nested enum
   sub-pattern in a payload position **always matches and never binds** on the
   native and JIT lanes — it would have matched `Const(Int(0), _)` too and left
   `name` unbound. See
   `.claude/memory/reference_enum_payload_subpattern_always_matches.md`.

Fixing only (1) would have replaced a dropped call with a *wrongly-targeted*
call. Both had to change together.

## Fix

Bind the constant in the outer arm and destructure it in a **second,
top-level** match:

```
case Const(const_value, _):
    match const_value:
        case Str(name):
            current_ctx = isel_add_extern(current_ctx, name)
            insts.push(new_mach_inst(X86_OP_CALL, [op_sym(name)]))
        case _:
            panic("x86_64 isel: call through non-symbol constant callee has no lowering")
```

Per the precedent in `4c140b35e1d` and
`_CBackendTranslate/class_core.spl:80` `emit_unsupported_panic`, the
unsupported case gets a hard failure rather than a plausible value — emitting a
`NOP` here is precisely the bug being fixed. `panic(...)` is already used as a
bare builtin elsewhere in this layer
(`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:549`).

`MirOperandKind` has exactly three variants and all three are now handled, so
the trailing `case _:` NOP arm is unreachable and was left as an exhaustiveness
backstop.

## Verification

**UNCOMPILED.** The deployed `bin/simple` has no `lint`/`test`/`run`
subcommands, and `src/compiler_rust/target/bootstrap/simple lint` on the edited
files did not return within the available window. The change is a static
correction validated against the enum definition and the anchored grep quoted
above; it has **not** been compiled or executed.

## Note on how this survived

An unresolved call in a `case` pattern produced no build failure and no
diagnostic. Combined with the sibling WASM defect and the dead `is_self_call`
in `mir_opt/tco.spl`, this is the third instance in one sweep of the same
family: **a `case` arm is not evidence that the arm ever runs.**
