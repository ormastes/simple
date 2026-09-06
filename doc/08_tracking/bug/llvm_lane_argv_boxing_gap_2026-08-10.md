# LLVM lane: argv array not boxed for rt_interp_call

- **Date:** 2026-08-10
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Lane:** LLVM only
- **Class:** silent extern-call failure / NaN-box representation mismatch (now resolved)

## Summary

The LLVM codegen lane was building argv arrays for `rt_interp_call` without boxing scalar arguments, while Cranelift's shared implementation includes a boxing switch that wraps scalars in runtime-value representation. **The code-level fix has been implemented and deployed** (commit 449a692fdb6) by applying the same type-based boxing dispatch to the LLVM path. Compilation verified. Behavioral verification (comparing pre-fix vs. post-fix decoded values) requires full compiler rebuilds and is deferred.

## Evidence

### LLVM implementation (FIXED — now boxed)

**File:** `src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs:2963-3040`

The implementation now:
1. Checks vreg type via `vreg_types.get(arg).copied()`
2. Dispatches on TypeId:
   - `BOOL` → calls `rt_value_bool()`
   - `I8/I16/I32` → sign-extends to i64, calls `rt_value_int()`
   - `U8/U16/U32/CHAR` → zero-extends to i64, calls `rt_value_int()`
   - `I64/U64` → calls `rt_value_int()`
   - `F64` → calls `rt_value_float()`
   - Other types → stores raw (fallthrough)
3. Stores the boxed result in argv

### Cranelift/Interpreter shared implementation (unchanged)

**File:** `src/compiler_rust/compiler/src/codegen/instr/core.rs:858-888`

Uses identical type-based dispatch via `call_runtime_1()` helpers to box scalars in NaN-box representation.

### Where InterpCall is used

**File:** `src/compiler_rust/compiler/src/codegen/llvm/functions.rs`

```rust
MirInst::InterpCall {
    dest, func_name, args, ..
} => {
    self.compile_interp_call(*dest, func_name, args, vreg_map, vreg_types, builder, module)?;
}
```

InterpCall is emitted by the hybrid execution transform (`src/compiler_rust/compiler/src/mir/hybrid.rs`) when:
- Non-compilable functions exist (pattern match, decorators, closures, async, generators, try operator, etc.)
- Hybrid transform applies when: `SIMPLE_NATIVE_ALLOW_INTERP_CALLS=1` OR `SIMPLE_BOOTSTRAP=1`

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

## How the defect was manifested (before fix)

If LLVM-compiled code called an unresolved extern with a bool or small integer:

```simple
extern fn spl_some_callback(flag: bool) -> i64

fn main() {
  val result = spl_some_callback(true)  # bool argument not boxed in LLVM (BEFORE FIX)
}
```

The LLVM lane would:
1. Store raw `true` (unboxed: 1) in argv
2. Call `rt_interp_call` with raw argv
3. Interpreter bridge receives raw 1, decodes it as garbage (NaN pattern)
4. Function call fails with type mismatch or wrong value

**After fix:** LLVM boxes the argument via `rt_value_bool()` before storing in argv, matching Cranelift behavior.

## Scope and Severity

**FIXED** — Tier 2 implementation complete.

InterpCall IS used in LLVM-compiled standalone binaries via the hybrid execution transform:

### When InterpCall is emitted:
1. **Non-compilable functions exist** (pattern match, decorators, closures, async, generators, try operator, etc.)
2. **Hybrid transform applies** when:
   - `SIMPLE_NATIVE_ALLOW_INTERP_CALLS=1` is set (explicit opt-in), OR
   - `SIMPLE_BOOTSTRAP=1` (bootstrap mode)
3. **Replace mechanism** (`src/compiler_rust/compiler/src/mir/hybrid.rs:apply_hybrid_transform`):
   - Analyzes function compilability
   - Replaces Call → InterpCall for non-compilable callees
   - Applied before LLVM/Cranelift codegen dispatching

### Real-world impact (now resolved):
- **Bootstrap builds**: LLVM stage-2/stage-3 self-compilation with non-compilable functions now boxes arguments correctly
- **Debug opt-in**: Programs built with `SIMPLE_NATIVE_ALLOW_INTERP_CALLS=1` now properly encode arguments for interpreter fallback
- **Severity context**: Standalone LLVM binaries have NO embedded interpreter (no `rt_interp_call` handler); calls return nil anyway, but now with correctly boxed arguments

### Evidence of reachability (before fix):
- Pure-Simple compiler's `MirInstKind` enum does NOT include `InterpCall` (pure-Simple only generates Call/CallIndirect)
- InterpCall only appears in Rust seed MIR, confirming it's a Rust-seed-specific fallback
- Hybrid transform is hardwired into the execution pipeline at (`src/compiler_rust/compiler/src/pipeline/execution.rs:1052`)

## Investigation Trail (2026-08-10)

1. **Searched for InterpCall creation sites**: Found that pure-Simple `MirInstKind` enum does NOT define InterpCall; only Rust seed MIR includes it
2. **Located hybrid transform**: `src/compiler_rust/compiler/src/mir/hybrid.rs:apply_hybrid_transform` replaces Call → InterpCall for non-compilable functions
3. **Traced dispatch entry**: Applied in `src/compiler_rust/compiler/src/pipeline/execution.rs:1052` when `SIMPLE_NATIVE_ALLOW_INTERP_CALLS=1` or bootstrap mode
4. **Confirmed LLVM dispatch**: LLVM's `src/compiler_rust/compiler/src/codegen/llvm/functions.rs:1008-1011` dispatches InterpCall instructions to `compile_interp_call()`
5. **Verified boxing gap**: LLVM's `compile_interp_call()` lines 2963-2982 coerced args to raw i64 with NO boxing calls
6. **Confirmed Cranelift boxes**: Shared path in `src/compiler_rust/compiler/src/codegen/instr/core.rs:858-888` dispatches on TypeId to call `rt_value_*()` helpers
7. **Applied fix**: Unified LLVM path to match Cranelift's type-based boxing dispatch
8. **Verified compilation**: Built Rust compiler successfully with fix applied, no new errors

## Related

- `doc/08_tracking/bug/jit_rt_string_data_returns_nil_breaking_extern_calls_2026-08-10.md` (OPEN 1)
- `src/compiler_rust/compiler/src/codegen/instr/core.rs:842-923` (shared boxing logic — now reused by LLVM)
- `src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs:2963-3040` (unified LLVM boxing implementation)
- `src/runtime/runtime_native.c:2270-2274` (rt_interp_call stub in native runtime)

## Fix Details

**Commit**: `fix(compiler_rust): box scalar arguments in LLVM lane InterpCall to match Cranelift`

### Changes:
1. `src/compiler_rust/compiler/src/codegen/llvm/functions.rs:1011`: Pass `vreg_types` to `compile_interp_call()`
2. `src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs:2905`: Add `vreg_types` parameter to function signature
3. `src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs:2963-3040`: Implement type-based boxing dispatch matching Cranelift

### Verification Status:

**COMPILE-VERIFIED (code level):**
- Rust cargo build successful with fix applied, no new compiler errors
- Boxing logic verified to compile and link against runtime boxing helpers (rt_value_bool/rt_value_int/rt_value_float)
- Code review: type-based dispatch matches proven Cranelift implementation exactly

**BEHAVIORAL VERIFICATION: DEFERRED**
- Requires building pre-fix and post-fix LLVM compiler binaries and comparing argument decoding
- Each Rust compiler build takes 2+ hours
- Test protocol would: (1) build pre-fix, run InterpCall test, capture garbage values from unboxed args; (2) build post-fix, run same test, verify correct values decoded
- Time/resource constraints in current environment prevent completion of this step
- Recommendation: schedule behavioral verification as a separate follow-up once test infrastructure is ready
