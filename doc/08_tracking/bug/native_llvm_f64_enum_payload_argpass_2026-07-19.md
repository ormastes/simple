# Native (LLVM) backend loses f64 enum payloads: construct passes in xmm0, extract sitofp-coerces

- **id:** native_llvm_f64_enum_payload_argpass_2026-07-19
- **status:** open
- **severity:** high (silent miscompile — wrong f64 value, no error)
- **backend:** native-build (LLVM) only. cranelift JIT and the MIR interpreter are correct.
- **class:** tag-box / enum-payload coercion (sibling of the `<<3` tagged-float mask leak, but a *different* root)

## Symptom

An `f64` carried as an enum/`Option`/`Result` single-field payload comes back as
the wrong value after a `native-build` compile. Fractional values with nonzero
low mantissa bits (e.g. `0.1`) and whole values alike are corrupted, because the
payload is effectively never delivered to the constructor.

Minimal repro (`tb_e28_enum_f64.spl`):

```simple
enum FBox:
    V(f64)

fn main() -> i64:
    val b = FBox.V(0.1)
    var r = 40
    match b:
        case FBox.V(x):
            if x == 0.1:
                r = 30
    return r
```

- interpreter / cranelift: `30` (correct)
- native-build (LLVM): `40` (payload lost)

## Root cause (disassembly evidence)

Two distinct LLVM-backend defects on the f64-enum payload path:

1. **Construct side — payload passed in the wrong register class.** At the
   `EnumWith` / `rt_enum_new` construct site the f64 payload is materialized in
   an XMM (float) register and the call is emitted with no bitcast into the
   integer argument register the runtime expects:

   ```
   movsd  <0.1>, %xmm0        ; payload in xmm0
   ...                        ; NO `movq %xmm0, %rdx`
   call   rt_enum_new         ; rdx (payload slot) holds garbage/stale
   ```

   `rt_enum_new` reads the payload as an i64 in `rdx`; because the f64 was left
   in `xmm0` and never bitcast to `rdx`, the stored payload is wrong — the value
   is lost *before* any extract runs.

2. **Extract side — numeric conversion instead of reinterpret.** The
   `rt_enum_payload` result (a raw i64 bit pattern) is coerced to f64 with
   `cvtsi2sd` (signed-int→double *numeric* convert) rather than a `movq`/bitcast
   reinterpret, so even a correctly-stored bit pattern would be re-interpreted as
   an integer-to-float conversion.

## Controls (what is NOT affected)

- plain f64 as a function parameter, struct field, or local: correct on native.
- i64 enum payloads: correct on native.
- Only **f64 enum/Option/Result payloads** break → isolates the defect to the
  enum-payload arg-passing/coercion, not general f64 codegen.

## Relationship to the 2026-07-19 MIR-lowering fix

The MIR-lowering fix in `mir/lower/lowering_expr_builtin.rs` (rt_enum_payload
extract: emit `Cast{F64→F64}` reinterpret instead of the `UnboxFloat` `(bits>>3)<<3`
mask) fixes the **extract-side mask** and makes the case correct on **cranelift +
interpreter**. It does not fix native-build, because native's construct side (#1)
loses the payload before extract runs — that is baseline behavior the MIR fix
does not touch, so **there is no regression** (native f64-enum was already broken).

## Fix sketch (LLVM backend, not MIR lowering)

- Construct: when an `EnumWith` payload arg is F64, `bitcast` f64→i64 (a `movq
  %xmm, %reg`) into the integer payload argument register before `call
  rt_enum_new`. Mirror whatever the i64 payload path already does.
- Extract: coerce the `rt_enum_payload` i64 result to F64 with a `bitcast`
  (`movq %reg, %xmm`), not `cvtsi2sd`.

## Regression guard

`test/03_system/native/option_box_unbox/` (or the tag-box test dir): keep
`tb_e28_enum_f64` XFAIL for native-build asserting the current wrong value, and
assert the correct value on the interp/cranelift path. Flip the native XFAIL to a
PASS when this backend fix lands.
