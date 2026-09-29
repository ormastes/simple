# Bug: JIT boxes i64 as `(value << 3) | TAG_INT` — drops the top 3 bits (bit-63 loss); miscompiles RV64 SoC

## Closed 2026-09-13 — fixed, re-verified by running the entry repro on both lanes

Verification engine: pinned copy of `src/compiler_rust/target/release/simple.exe`
(Simple Language v1.0.1-beta.1, 39,267,840 bytes, sha256 prefix `1b62a1a42755774fc087`,
built 2026-09-13 on this host). Windows 11 / Git Bash, default `run` lane
(seed JIT with interpreter fallback). This is the **Rust bootstrap seed**, not a
deployed pure-Simple self-hosted binary — the self-hosted lane remains unverified
on this host.

Ran the minimal reproducer shape from this entry (the array-in-struct boxed
path it isolates as the ONLY corrupting shape), plus the bare-local control
and the bootrom `slli sp,sp,32` roundtrip:

```spl
struct Outer:
    arr: [i64]

fn shifty(v: i64, n: i64) -> i64:
    v << n

fn main():
    var o = Outer(arr: [0, 0, 0])
    o.arr[2] = 0x8010000000000000
    print("{o.arr[2]}")
    o.arr[0] = shifty(1, 63)
    o.arr[1] = shifty(1, 62)
    print("{o.arr[0]} {o.arr[1]}")
    var sp = shifty(0x80100000, 32)
    print("{sp} {sp >> 32}")
```

Seed JIT lane and tree-walk lane produce **identical, correct** output:

```
-9218868437227405312          # o.arr[2] == 0x8010000000000000, bit 63 intact
-9223372036854775808          # 1 << 63, was reported to box to 0
4611686018427387904           # 1 << 62, was reported to box to 0
-9218868437227405312 -2146435072   # slli sp,32 roundtrip, no 0x100000 derail
```

The three failure signatures this entry names — bit-63 loss through the
struct-field `[i64]` boxed path, `1<<63`/`1<<62` boxing to `0`, and the
`0x8010000000000000 -> 0x0010000000000000` `sp` corruption — none reproduce.
The boxed integer channel is 64-bit clean on this binary; the JIT no longer
diverges from the interpreter on any of them (measured, both lanes).

Cross-reference: a **different** defect in the same tagged-value scheme is
still live and was found while re-verifying this one — `Some(x)` pattern
destructuring on the JIT lane binds `payload << 3` (the still-tagged word,
i.e. a missing unbox rather than a lossy box). Filed as
`doc/08_tracking/bug/jit_some_pattern_payload_shifted_left_3_2026-09-13.md`.
That the general channel is now 64-bit clean while `Some(x)` is still shifted
shows the two are separate sites, not one root cause.

- **ID:** seed_jit_boxed_int_61bit_drops_high_bits
- **Date:** 2026-07-22
- **Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed) — CLOSED 2026-09-13 (see top section)
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

## DEFINITIVE DIAGNOSIS (2026-07-22, Option-B implementation attempt)
Attempted the "narrow" fix (regfile/RAM typed `[u64]` + widen the `[u64]` store
gate + preserve `U64_PACKED` through `rt_array_copy`/`rt_array_concat`), built the
seed (cargo, exit 0), and validated. **It did NOT fix the JIT truncation.**
Empirical findings, all with the freshly-built seed:

- **2×2 (scalar/array × i64/u64):** under JIT ONLY array elements drop bit 63;
  scalar locals, scalar struct fields, and fn-returns all preserve bit 63.
  Under interp everything is correct.
- **Plain `[u64]` ALSO truncates under JIT** — `[u64]` is NOT a "working path".
  It only packs (`U64_PACKED`) when the literal's elements are statically
  `TypeId::U64` OR the array-literal `expr_ty` is `[u64]`. For `var a: [u64] =
  [0,0]` and `var regs: [u64] = []` the annotation does NOT reach
  `lower_array_expr`'s `outer_ty` (MIR dump shows `BoxInt` per element → generic
  non-packed array). So the store/read correctly route to
  `rt_typed_words_u64_set`/`_at`, but on a NON-packed array those re-box via the
  lossy 61-bit `from_int`/`as_int` (collections.rs:892 / maybe_packed load-store
  `select(is_packed,...)` picks the tagged arm). Value observed:
  `0x8010000000000000 → 0x0010000000000000` = one `<<3>>3` round trip.
- **Interp is immune because its arrays store native i64 losslessly** — packing
  is a native/JIT-only concept.

**Packing is whack-a-mole.** Making `[u64]`/`[i64]` reliably packed needs, so
far: (1) store-gate widen [done], (2) `rt_array_copy` packing-preserve [done,
correct in isolation], (3) `rt_array_concat` packing-preserve [done, correct in
isolation], (4) creation-site type-propagation so annotated `[u64]`/`[i64]`
literals+empties actually pack [NOT done] — and still lurking: slices,
fn-returns-of-arrays, dict values, and every `as_slice()` consumer. Four+ sites
for one bug ⇒ wrong-shaped approach. If a JIT fix is ever required, **Option A
(HeapInt, lossless boxing) is the correct single-representation fix**, not
finishing packing — but it is a full-bootstrap core change with the hot-path
cost noted above and must go back to the requester with this scope.

## OFF THE CRITICAL PATH (why this is deferred, not shipped)
`soc_top_64` runs three ways: interp (correct, slow), JIT (fast, THIS bug), and
VHDL-synth→FPGA (the actual `/goal` board target). The boxed-int representation
lives ONLY in the Simple runtime; the VHDL backend emits `std_logic_vector`
hardware and never sees a `RuntimeValue`. So this bug does not affect the FPGA /
board deliverable, and the RTL model's correctness is already validated by the
interp test pass. It is a JIT-simulation performance/correctness follow-up, not
a board blocker. (Also: `build/os/opensbi_rv64_soc/fw_payload.bin` is absent in
this environment, so the real OpenSBI banner is unreachable here under interp OR
JIT regardless of this fix.)

Reviewer did NOT land the packing changes — the JIT still truncates, so shipping
them under a "boxed-int fixed" message would be a false-green. The `copy`/
`concat` packing-preserve edits are correct in isolation and are preserved in
worktree `/tmp/wt_heapint` should Option-B-complete or Option-A ever be
authorized.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
