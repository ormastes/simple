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

## CORRECTION (2026-07-22, implementation attempt) — no heap-int primitive exists

An earlier version of this doc claimed `rt_value_int` "stores the full i64" and
the fix was to route large ints through it. **That is wrong.** Source of truth
`runtime/src/value/core.rs:200`:
```
pub fn from_int(i: i64) -> Self { Self((i as u64) << 3) }   // 61-bit, lossy
pub fn as_int(self) -> i64 { (self.0 as i64) >> 3 }
```
The runtime `RuntimeValue` integer channel is itself 61-bit by design
(core.rs:19 "Full 61-bit integer range", :197 "Only 61-bit signed integers can
be stored directly. Larger integers would need heap allocation"). `rt_value_int`
does NOT heap-box — it would lose bit 63 too. So the fix cannot just call an
existing primitive; it must ADD one.

## The two real fixes (each core; each needs a full seed rebuild + T3 bootstrap)

### Option A — add a `HeapInt` type (mirror the in-tree `HeapFloat`)
`HeapFloat` (heap.rs:44,68; core.rs:232 `from_float`) already solved the exact
analogue for floats: inline `TAG_FLOAT` was lossy, so floats now allocate a
`HeapFloat` leaf storing the full f64 and return a tagged heap pointer,
disambiguated by an O(1) `HEAP_ALLOCATION_REGISTRY` membership check
(`as_heap_float_ptr`, heap_type==Float). Mirror it: `HeapObjectType::Int`,
`HeapInt{header,value:i64}`, `from_int` heap-boxes when `(i<<3)>>3 != i`,
`as_int`/`is_int`/`heap_type`/eq/display/truthy/clone-drop handle it, and the 3
JIT box sites (instr/mod.rs:1384, cranelift_emitter.rs:728, mir_interpreter.rs:759)
+ unbox counterparts route large ints through the runtime. General — also fixes
the `print("{x}")` bit-63 case. Blast radius: the value core used by the whole
toolchain and every compiled program.

### Option B — raw-pack `[i64]` arrays (`U64_PACKED`)
`mir/lower/lowering_expr_collection.rs:140` only raw-packs an array when every
element is `TypeId::U64` OR the outer declared type is `[u64]`; `[i64]` falls to
the DEFAULT tagged-RuntimeValue-slot path (61-bit → bit-63 loss on element
store). The regfile is `regs: [i64]`, so its slli-by-32 results lose bit 63.
Fix: treat `[i64]` (and `[i32]`?) like `[u64]` for raw packing (add
`outer_is_i64_array` + `elem.ty == I64`). More localized to the failing path,
but changes array storage semantics that generic consumers (iteration, equality,
print, the `maybe_packed_u64_load/store` guards in calls.rs) must all already
honor — needs a full-suite regression to prove no `[i64]`-array behavior breaks.
NOTE: a bare-local `[i64]` element store was OBSERVED correct in the repro while
the struct-field one was not — so the packing decision already diverges by
context (local annotation vs struct-literal field init); the fix must make both
paths agree on raw packing.

## Status
Root cause fully bisected and now accurately sourced. Both fixes are core
changes requiring a cargo seed rebuild + T3 bootstrap + full-suite regression to
land safely — not shippable as a blind autonomous push. Reviewer paused
implementation here to confirm approach (A vs B) and the bootstrap cycle with
the requester rather than risk a toolchain-wide-corrupt binary.
