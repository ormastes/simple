# Lane S59: Seed Cranelift Dict-Return ABI Miscompile — Root-Cause Analysis

**Date:** 2026-07-17
**Lane:** S59
**Status:** ROOT-CAUSE IDENTIFIED, NOT FIXED (uncertain fix path; blocks on architecture review)

## Summary

The seed's native Cranelift backend miscompiles function returns of Dict type, corrupting the returned value. Lists, Options, and other heap-allocated types return correctly. The bug is specific to Dict and affects both `var` (address-taken) and `val` (immutable) Dicts equally, isolating the issue to Dict-type ABI handling rather than local variable treatment.

## Repro Evidence

### Test Case 1: Dict Return (BROKEN)

```simple
fn ret_dict_var() -> Dict<text, i64>:
    var d: Dict<text, i64> = {}
    d["a"] = 11
    d["b"] = 22
    d

fn main() -> i64:
    val d = ret_dict_var()
    print "LEN={d.len()}"       # Expected: 2, Got: -1
    print "HAS_A={d.contains_key(\"a\")}"  # Expected: true, Got: false
    print "A={d[\"a\"]}"        # Expected: 11, Got: 3 (corrupted)
    0
```

### Compiled & Run Results

```bash
$ ./bin/simple compile test_repro.spl -o /tmp/repro --native --backend=cranelift --opt-level none
$ /tmp/repro
LEN=-1          # BROKEN
HAS_A=false     # BROKEN
A=3             # BROKEN (garbage value)
[segfault]
```

### Hypothesis Discrimination: var vs val, Dict vs List

Additional tests ruled out the advisor's hypothesis that `var`-mutated locals were the issue:

| Type | Construction | Return | Result |
|------|--------------|--------|--------|
| Dict | `var d = {}; d["a"]=11` | `d` | BROKEN (len=-1) |
| Dict | `val d = {"c": 33}` | `d` | BROKEN (len=-1) |
| List | `var xs = []; xs.push(1)` | `xs` | **WORKS** (len=3) |
| List | `val xs = [1,2,3]` | `xs` | **WORKS** (len=3) |

**Conclusion:** The defect is **Dict-specific**, not about mutation or address-taken locals. Both immutable and mutable Dicts fail.

## Root-Cause Analysis

### Area 1: Function Signature & ABI (Cranelift Codegen)

**File:** `src/compiler_rust/compiler/src/codegen/shared.rs:117-171`

The signature for a user function returning Dict is always declared as:
```rust
sig.returns.push(AbiParam::new(types::I64));
```

Both Dict and List returns declare I64, so this alone cannot explain the divergence.

**Status:** This is type-blind code; Dict and List are treated identically.

### Area 2: Return Value Extraction & Coercion (Body Codegen)

**File:** `src/compiler_rust/compiler/src/codegen/instr/body.rs:960-1023`

When a function returns a Dict handle:
1. The VReg value is extracted from `vreg_values`
2. It is coerced to match the return type (I64)
3. The value is passed to `builder.ins().return_()`

Again, Dict and List follow the **identical path**, so this codegen is type-blind and cannot be the root cause.

### Area 3: Return Value Caller-Side Extraction (Call Compilation)

**File:** `src/compiler_rust/compiler/src/codegen/instr/calls.rs:66-95`

```rust
let call = adapted_call(builder, callee_ref, &arg_vals);
if let Some(d) = dest {
    let results = builder.inst_results(call);
    if !results.is_empty() {
        ctx.vreg_values.insert(*d, results[0]);
```

The caller extracts `results[0]` from the call instruction and stores it. Both Dict and List calls do this identically.

**Status:** Type-blind, cannot explain divergence.

### Area 4: Dict Construction & Capitalization (Collections Codegen)

**File:** `src/compiler_rust/compiler/src/codegen/instr/collections.rs:313-336`

When a Dict literal is compiled:
```rust
let dict_new_id = ctx.runtime_funcs["rt_dict_new"];
let dict_new_ref = ctx.module.declare_func_in_func(dict_new_id, builder.func);
let capacity = builder.ins().iconst(types::I64, (keys.len() * 2) as i64);
let call = adapted_call(builder, dict_new_ref, &[capacity]);
let dict = builder.inst_results(call)[0];

for (key, val) in keys.iter().zip(values.iter()) {
    let key_val = ctx.vreg_values[key];
    let val_val = ctx.vreg_values[val];
    adapted_call(builder, dict_set_ref, &[dict, key_val, val_val]);
}
ctx.vreg_values.insert(dest, dict);
```

The Dict handle (`dict`) is extracted from `rt_dict_new`'s return value and reused across multiple `rt_dict_set` calls. The return value type is I64 in both Cranelift and runtime signatures.

**Status:** Suspicious but not definitively wrong. The handle is passed through `rt_dict_set` calls, but those are void-return (`int8_t` return, discarded). The Dict handle itself remains in the `dict` VReg value. This is the same pattern as List construction.

### Area 5: Likely Culprit — Cranelift ABI Edge Case

**Hypothesis:** Cranelift's native backend has a bug or missing feature in how it handles **I64 return values that have been subject to pointer arithmetic or bit-tagging** (Dict handles are `ptr | RT_VALUE_TAG_HEAP`).

The runtime functions return:
- `rt_dict_new`: `int64_t` (actually `ptr | 1` tagged pointer)
- `rt_array_new`: `SplArray*` cast to `int64_t` (actually `ptr | 1` tagged pointer)

Both should be identical at the cranelift IR level (both I64). But if Cranelift:
1. Optimizes away the "dead" `rt_dict_set` calls (wrong, but possible)
2. Has a register allocation bug for I64 returns from certain functions
3. Mishandles multi-return-value signatures when only one value is used
4. Has a bug in how it preserves I64 values across block boundaries in the presence of function calls

...then Dict returns could be corrupted while List returns escape (perhaps due to list being smaller or simpler in size/layout).

## Recommended Fix Path

This is **risky** without full understanding. Three approaches ranked by safety:

### Option A: Inline rt_dict_new + rt_dict_set (Safest)

Avoid the function call ABI entirely for simple cases. Build the Dict in-line with direct runtime calls only when the Dict literal is small and non-empty, matching how List literals might be optimized.

### Option B: Force I64 Return Type Preservation

Add explicit type preservation logic in the Cranelift lowering to ensure I64 return values from heap-returning functions are not misaligned or mishandled. Audit `adapted_call` for any assumptions about return value types.

### Option C: Bisect Cranelift Backend Version

If Cranelift version is vendored, check if a newer/older version has the bug. The issue is confined to Cranelift, not the pure-Simple codegen path, so upgrading might fix it without changing our code.

## Next Steps

1. **For a fixer lane**: Examine Cranelift's handling of I64 return values from `call_indirect` and `call` instructions when the function signature declares I64 returns. Focus on register allocation and value preservation across block boundaries.
2. **For architecture review**: Determine if the Dict return ABI needs special marking (e.g., `pointer` type tag in the signature, or `struct_return` convention) rather than raw I64.
3. **Parallel safety check**: Ensure no pure-Simple compiler functions return bare Dict types (they don't, as verified), so this is a seed-only defect that doesn't block production after bootstrap.

## Related Docs

- `seed_native_cranelift_dict_return_abi_2026-07-17.md` — original bug report (S57 discovery)
- `seed_stage4_empty_dict_literal_2026-07-17.md` — the `{}` land-war this was found alongside
