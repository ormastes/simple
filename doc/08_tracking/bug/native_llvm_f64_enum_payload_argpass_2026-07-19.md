# Native (LLVM) backend loses f64 enum payloads: construct passes in xmm0, extract sitofp-coerces

- **id:** native_llvm_f64_enum_payload_argpass_2026-07-19
- **status:** source fixed; incremental LLVM execution pending
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

`test/03_system/native/enum_f64_payload_precision.spl` returns 30 only when the
LLVM constructor and extractor preserve the payload bits. The interpreter /
Cranelift control remains in
`test/01_unit/compiler/codegen/enum_f64_payload_precision_spec.spl`.
The shared native smoke matrix schedules the system fixture on Linux, macOS,
Windows, and FreeBSD; hosted Cranelift remains the control backend.

## Source fix

The pure-Simple LLVM backend now reuses its aggregate float-word helper for the
third `rt_enum_new` argument. On extraction, MIR lowering emits an explicit
i64-to-f64 bitcast only where the enum/Option/Result payload's semantic type is
f64. An i64 enum payload later cast with `as f64` remains an ordinary numeric
`sitofp` conversion.

The direct LLVM-IR regression constructs both runtime calls, rejects
`fptosi`/`sitofp` on the f64 payload path, and requires `sitofp` for a normal
i64-to-f64 cast. A cache-isolated current-source mini build was
bounded at 4 GiB and 240 seconds; it reached the time cap with no output, so a
fresh native executable is not claimed.
