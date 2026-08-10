# LLVM lane: argv array not boxed for rt_interp_call

- **Date:** 2026-08-10
- **Status:** **CONFIRMED STRUCTURAL GAP** — the code path exists and is unboxed. Whether it manifests as a real defect is **unmeasured** (LLVM-compiled programs may not exercise this code path in practice).
- **Lane:** LLVM only
- **Class:** potential silent extern-call failure / NaN-box representation mismatch

## Summary

The LLVM codegen lane builds argv arrays for `rt_interp_call` without boxing scalar arguments. Cranelift's shared implementation includes a boxing switch that wraps scalars in runtime-value representation before passing them to the interpreter bridge. This gap means if an LLVM-compiled function calls an unresolved extern function, the arguments may be decoded incorrectly by the interpreter.

## Evidence

### LLVM implementation (unboxed)

**File:** `src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs:2963-2982`

```rust
for (index, arg) in args.iter().enumerate() {
    let value = self.get_vreg(arg, vreg_map)?;
    let casted = self.coerce_value_to_type(value, Some(i64_type.into()), builder)?;
    // ... pointer math ...
    builder
        .build_store(typed_ptr, casted)
        .map_err(|e| crate::error::factory::llvm_build_failed("store", &e))?;
}
```

The loop:
1. Gets the vreg value
2. Coerces to i64
3. Stores raw with no boxing helper calls

### Cranelift/Interpreter shared implementation (boxed)

**File:** `src/compiler_rust/compiler/src/codegen/instr/core.rs:858-888`

```rust
for (index, arg) in args.iter().enumerate() {
    let mut arg_val = match ctx.vreg_values.get(arg) { /* ... */ };
    match ctx.vreg_types.get(arg).copied() {
        Some(TypeId::BOOL) => {
            arg_val = call_runtime_1(ctx, builder, "rt_value_bool", arg_val);
        }
        Some(TypeId::I8 | TypeId::I16 | TypeId::I32) => {
            // sign-extend, then box
            arg_val = call_runtime_1(ctx, builder, "rt_value_int", arg_val);
        }
        Some(TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::CHAR) => {
            // zero-extend, then box
            arg_val = call_runtime_1(ctx, builder, "rt_value_int", arg_val);
        }
        Some(TypeId::I64 | TypeId::U64) => {
            arg_val = call_runtime_1(ctx, builder, "rt_value_int", arg_val);
        }
        Some(TypeId::F64) => {
            arg_val = call_runtime_1(ctx, builder, "rt_value_float", arg_val);
        }
        _ => {}  // <-- Fallthrough for unknown types (partial gap even in Cranelift)
    }
    builder.ins().store(MemFlags::new(), arg_val, argv, (index * 8) as i32);
}
```

Cranelift calls runtime boxing helpers: `rt_value_bool`, `rt_value_int`, `rt_value_float` which encode values in NaN-box representation.

### Where InterpCall is used

**File:** `src/compiler_rust/compiler/src/codegen/llvm/functions.rs`

```rust
MirInst::InterpCall {
    dest, func_name, args, ..
} => {
    self.compile_interp_call(*dest, func_name, args, vreg_map, builder, module)?;
}
```

InterpCall is dispatched for extern functions that are not resolved at compile time. In LLVM-compiled binaries, this occurs when:
- A function calls an `extern` function
- The symbol is not statically linked
- The runtime falls back to interpreter bridge via `rt_interp_call`

## Boxing functions

**File:** `src/runtime/runtime_native.c`

```c
int64_t rt_value_bool(int64_t value) {
    return rt_core_from_special(value ? RT_VALUE_SPECIAL_TRUE : RT_VALUE_SPECIAL_FALSE);
}

int64_t rt_value_int(int64_t value) {
    if (!rt_core_int_fits_tagged(value)) return rt_value_int_wide(value);
    return (int64_t)(((uint64_t)value << 3) | RT_VALUE_TAG_INT);
}

int64_t rt_value_float(int64_t raw_bits) {
    RtCoreFloat* f = (RtCoreFloat*)malloc(sizeof(RtCoreFloat));
    if (!f) {
        return (int64_t)(((uint64_t)raw_bits & ~RT_VALUE_TAG_MASK) | RT_VALUE_TAG_FLOAT);
    }
    // ... heap allocation ...
}
```

These functions wrap raw scalars in the NaN-box encoding (tag bits and immediate values or pointers). The interpreter's `rt_interp_call` handler expects boxed values.

## How the defect would manifest

If LLVM-compiled code calls an unresolved extern with a bool or small integer:

```simple
extern fn spl_some_callback(flag: bool) -> i64

fn main() {
  val result = spl_some_callback(true)  // bool argument not boxed in LLVM
}
```

The LLVM lane would:
1. Store raw `true` (unboxed: 1) in argv
2. Call `rt_interp_call` with raw argv
3. Interpreter bridge receives raw 1, decodes it as garbage (NaN pattern)
4. Function call fails with type mismatch or wrong value

## Scope and Severity

**UNMEASURED:** This is a structural gap in the code, but whether it affects real LLVM-compiled programs is unknown:

- LLVM may always link unresolved externs statically, avoiding InterpCall entirely
- InterpCall may only be used in hosted interpreter mode, not native LLVM output
- Existing tests may not exercise InterpCall from LLVM-compiled code

**Verification needed:**
- Does LLVM-compiled code ever actually execute `MirInst::InterpCall`?
- Test: LLVM-compiled program calling an unresolved extern function
- Compare argv decoding between LLVM (unboxed) and Cranelift (boxed)

## Related

- `doc/08_tracking/bug/jit_rt_string_data_returns_nil_breaking_extern_calls_2026-08-10.md` (OPEN 1)
- `src/compiler_rust/compiler/src/codegen/instr/core.rs:842-923` (shared boxing logic)
- `src/runtime/runtime_native.c:2270-2274` (rt_interp_call stub in native runtime)

## Recommendations

1. **Tier 1 — Reproduce:** Build LLVM test binary that calls unresolved extern with bool/int args. Run both LLVM and Cranelift lanes. Compare argv decoding in interpreter bridge.
2. **Tier 2 — Root cause:** If reproduced, apply boxing helpers to LLVM's `compile_interp_call` (lines 2963-2982) to match Cranelift's switch.
3. **Tier 3 — Gate:** Add test to prevent regression (e.g., `check-llvm-interp-call-boxing.shs`).
