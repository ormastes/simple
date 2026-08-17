# Bug: JIT boxes i64 as `(value << 3) | TAG_INT` — drops the top 3 bits (bit-63 loss); miscompiles RV64 SoC

## VERIFIED FIXED 2026-08-17 — and now actually covered by tests

Classified by content (brief correction #1). `RuntimeValue::from_int`
(`src/compiler_rust/runtime/src/value/core.rs:260`) now range-checks before
boxing: values that round-trip keep the bit-identical inline `i << 3`, and
anything outside it goes to `from_wide_int`, which heap-boxes a full-width i64.
`fits_inline_int` is written as an explicit `[-(1<<60), (1<<60)-1]` range test
rather than `(i << 3) >> 3 == i`, because that shift overflows for exactly the
inputs being screened.

**The fix had ZERO test coverage.** `grep -rn 'from_wide_int|fits_inline_int'`
across `src/compiler_rust/` returned only the definitions in `core.rs` itself —
no caller, no test — so a revert would have been silent. Added
`src/compiler_rust/runtime/tests/boxed_int_wide_roundtrip.rs`:

- the four values named in this report (`0x8010000000000000`, `2^62`,
  `i64::MAX`, `i64::MIN`), each additionally asserted NOT to equal what the
  pre-fix encoding produced, so the test cannot pass vacuously
- a class sweep: every power-of-two magnitude and neighbour, both signs, plus
  all-ones and alternating bit patterns, straight across the 2^60 boundary —
  asserting the representation actually CHOSEN alongside the value, so a wide
  value cannot claim to be an inline int while holding a truncated payload
- `fits_inline_int` checked against the raw encoding's real capacity, computed
  independently of its own range constants

```
Results: 3 passed; 0 failed; 0 ignored
  cargo test -p simple-runtime --test boxed_int_wide_roundtrip
```

The crate sets `autotests = false`, so the `[[test]]` block in
`runtime/Cargo.toml` is required or the file is silently never compiled.

## VERIFIED FIXED 2026-08-17 (batch_02 core-silent-wrong lane)

Fixed by `2a240d9b0b2` ("fix(jit): i64 values >= 2^60 silently became a
different number"), which routes wide values to a signed heap box
(`HeapObjectType::Int`) and keeps the bit-identical `i << 3` fast path for
values that fit.

**This doc is a worked example of the stale-binary trap, and the evidence is
kept here deliberately.** The doc's own reproducer — an `[i64]` array that is a
struct field — was run against two binaries on the same tree:

| binary | `o.arr[2] = 0x8010000000000000` under JIT | interpreter |
|---|---|---|
| deployed `bin/simple`, mtime 2026-08-16 22:59 | `4503599627370496` (**bit 63 dropped**) | `-9218868437227405312` |
| freshly built from `88227f48202`, this session | `-9218868437227405312` (correct) | `-9218868437227405312` |

A second control in the same probe, `w[0] = 1<<62`, read back `0` on the
deployed seed and `4611686018427387904` on the fresh one — matching this doc's
"`1<<63` and `1<<62` box to 0" prediction exactly.

The deployed seed was built at 22:59 on 2026-08-16; `2a240d9b0b2` landed at
06:23 on 2026-08-17. Anyone reproducing against the deployed `bin/simple` will
therefore still see the original, fully convincing failure. Closeable.

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

## 2026-08-17 — Option A DID land, then was silently REVERTED by a stale snapshot

Classification by CONTENT (not SHA), triage shard A6:

- `2a240d9b0b2` "fix(jit): i64 values >= 2^60 silently became a different number"
  implemented exactly the Option-A HeapInt fix recommended above, across 10
  Rust files, plus 4 spec files.
- The very next commit touching those files, `e14a2ffb4df`
  ("fix(backend,mir): three fail-open sites made fail-closed"), reverted **all
  ten** source files to their pre-fix content — the stat lines are the exact
  inverse (`core.rs 104 +++/---`, `closures_structs.rs 51`, `methods.rs 37`,
  `heap.rs 24`, `transfer.rs 44`, ...). It is a whole-working-copy stale-snapshot
  clobber of the kind `.claude/rules/vcs.md` § "Sync must never clobber"
  forbids; the same commit also deleted `src/compiler/35.semantics/lint/
  silent_default.spl` (341 lines), `scripts/check/check-silent-default-baseline.shs`,
  and gutted `scripts/check/check-engine-differential.shs` (411 lines).
- Evidence at HEAD (`b32ec0de65a`):
  `git show HEAD:src/compiler_rust/runtime/src/value/core.rs | grep -c fits_inline_int` -> `0`
  and `from_int` at core.rs:240-243 is again the bare `Self((i as u64) << 3)`.
- The four spec files added by `2a240d9b0b2` SURVIVED (the revert hit source
  only), so `test/01_unit/compiler/codegen/probe_wide_int_boundary_jit.spl` and
  `wide_int_boundary_class_spec.spl` are live reproducers against HEAD.

Status: **LIVE at HEAD, cause = revert, not a missing fix.** The 10 Rust files
have been restored from `2a240d9b0b2` into the working tree (uncommitted) and
`cargo check --release --bin simple` passes clean on the restored tree.
