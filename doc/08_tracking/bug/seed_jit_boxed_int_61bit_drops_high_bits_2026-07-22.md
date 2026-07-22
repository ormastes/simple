# Bug: JIT boxes i64 as `(value << 3) | TAG_INT` — drops the top 3 bits (bit-63 loss); miscompiles RV64 SoC

- **ID:** seed_jit_boxed_int_61bit_drops_high_bits
- **Date:** 2026-07-22
- **Status:** OPEN — ROOT CAUSE FULLY BISECTED; fix is a core value-representation change (awaiting go-ahead)
- **Severity:** high — root cause of the soc_top_64 JIT miscompile (57 probe failures) and the OpenSBI-banner block
- **Component:** seed JIT value boxing (`src/compiler_rust/compiler/src/codegen`)

## Root cause (bisected from soc_top_64_probe case3)
The seed's tagged RuntimeValue **inline** representation boxes an integer as
`(value << 3) | TAG_INT(0)` and unboxes as `value >> 3`. That is a **61-bit**
integer channel: any i64 that uses the top 3 bits is corrupted.
- `0x8010000000000000 << 3 >> 3 = 0x0010000000000000` (bit 63 lost) — exactly the
  observed `sp` corruption (0x80100000 -> 0x100000 through the bootrom slli/srli).
- `1<<63` and `1<<62` box to `0`.

## Minimal reproducer (scratchpad/repro_jit_bit63.spl)
```
struct Outer:
    arr: [i64]
...
o.arr[2] = 0x8010000000000000
# JIT: o.arr[2] == 0x0010000000000000  (bit 63 dropped)
# interp: o.arr[2] == 0x8010000000000000  (correct)
```
Same-mode control isolates it precisely — under JIT:
- bare local `[i64]` element store/load: **correct** (stays unboxed native i64)
- struct **scalar** i64 field: **correct**
- fn param/return i64: **correct**
- **`[i64]` array that is a struct field (`o.arr[i]`): bit 63 DROPPED** ← boxed path
- ALU `op_a << shamt` and the sll/srl roundtrip in isolation: **correct**
`soc3.core.rf.regs[2]` is exactly the array-in-struct shape, so the bootrom's
`slli sp,sp,32` result (0x8010000000000000) is dropped to 0x0010000000000000,
`srli` -> 0x100000, and the boot derails (pc below RAM). Also explains the
cosmetic `print("{x}")` bug (interpolation args transit the same boxed channel):
a bit-63 i64 prints as 0 while comparing correctly (raw-print boxed, `==` unboxed).

## Exact code sites
- `codegen/instr/mod.rs:1384` — `let boxed = builder.ins().ishl(val, three);` (main cranelift JIT BoxInt; **no overflow handling**)
- `codegen/cranelift_emitter.rs:728` — `let boxed = self.builder.ins().ishl(val, three);`
- `codegen/mir_interpreter.rs:759` — `self.set(dest, self.get(value) << 3);`
- Unbox counterparts: `UnboxInt` at instr/mod.rs:1409 (`>> 3`, passes TAG_HEAP through verbatim), plus the cranelift_emitter / mir_interpreter equivalents.

## The fix (precedent already in-tree)
`BoxFloat` (instr/mod.rs:1388) was ALREADY changed away from the lossy inline
`(bits>>3)<<3|TAG_FLOAT` to **heap-box the full 64-bit value** via
`rt_value_float`, because inline boxing was lossy. Mirror that for ints:
- BoxInt: if `(val << 3) >> 3 == val` (fits 61-bit signed) keep the fast inline
  `<< 3`; else heap-box via `rt_value_int(val)` (exists:
  `interpreter_extern/sffi_value.rs:25`; runtime stores the full i64).
- UnboxInt: tagged scalar (low3==0) shifts `>> 3` as today; a HEAP value must be
  disambiguated — heap-boxed-int -> `rt_value_as_int`, enum/struct handle ->
  pass through verbatim. Runtime helpers `rt_value_is_int`/`rt_value_is_heap`/
  `rt_value_type_tag` exist for this.
- Apply symmetrically at all 3 box + 3 unbox sites (cranelift x2 + mir_interpreter).

## RISK (why confirm before landing)
This mutates the compiler's **core integer value representation**, used by every
boxed int in the self-hosted compiler AND every program it compiles. The
UnboxInt heap disambiguation is the exact spot that already produced two logged
defects — DEFECT A (`>>3` mangled a heap enum pointer) and DEFECT B (re-boxing a
heap handle shifted its TAG_HEAP away). A subtle error here reintroduces
enum/heap-handle corruption toolchain-wide. It also requires a full seed cargo
rebuild + T3 bootstrap to validate/deploy (bootstrap.md), and a wrong build
ships a corrupt compiler. The conditional (only heap-box >61-bit values) keeps
the common path byte-identical, which bounds the blast radius — but the change
is still core.

## Safer alternative
Keep the protective `lsu64_load`/`len` lowering fallback (soc_top_64 stays on the
correct interpreter) and reach the banner via the **self-hosted native
compiler** deploy instead — its native path uses the runtime's correct
`rt_value_int` boxing, not the JIT inline `<<3`. That is the other filed blocker
but avoids core-representation surgery on the seed.

## Cross-refs
[[seed_jit_miscompiles_soc_top_64_masked_by_fallback]],
[[seed_jit_lsu64_load_lowering_forces_interpreter]].
