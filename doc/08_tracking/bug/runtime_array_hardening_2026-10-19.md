# Array semantics hardening across interpreter, JIT and native

**Status:** 7 FIXED, 3 RECORDED (branch `work/runtime-array-hardening`, base
`origin/release_phase3` @ `ea83abd9595`, which includes PR #3779).
**Found while fixing:** `native_index_get_packed_raw_slot_2026-10-19.md`
("Still open" list) and the review of PR #3779.

Packed layouts: `[u8]` is BYTES (1 raw byte per element) and `[u64]` is
U64_PACKED (1 raw word per element). Generic arrays hold 8-byte tagged slots.
Values of 2^60 or more do not fit the tagged immediate, so they are
heap-boxed: a signed wide box (`rt_value_int_wide`, Rust `HeapInt`) or a u64
box (`rt_value_u64`, Rust `HeapUInt`).

## 1. Join read packed arrays as 8-byte slots (native) — FIXED

- `rt_string_join` (the seed's native `.join`) and `rt_array_join_any` (the
  self-hosted compiler's runtime-array join) in `src/runtime/runtime_native.c`
  read `((int64_t*)data)[i]` without checking the layout. On a `[u8]`, that is
  a heap-buffer-overflow read (ASan, red on base). Integer elements also
  rendered as `""`, so `[65u8, 66u8, 67u8].join(",")` printed `,,`. Rust
  renders them with `rt_value_to_string`.
- Rust `rt_array_join` (LLVM backend) had the same `as_slice()` read.
- Fix: elements are read through `spl_core_slot_value`, which reads at the
  element's own width and tags the value. Non-text elements are rendered with
  `rt_to_string`, once per element.

## 2. RuntimeValue writes stored tagged values raw into `[u64]` (native) — FIXED

- `data[i] = 56` / `data.push(9)` on an untyped `[u64]` read back as 448 / 72.
  `rt_index_set` and `rt_push` are the entry points that receive a RuntimeValue.
  They forwarded it to `rt_array_set` / `rt_array_push`, which store a raw word
  for U64_PACKED. That raw-word contract pairs with `rt_array_get`'s raw read
  and is pinned by `rt_array_packed_reverse_index_enumerate_selfcheck.c`.
- Fix: `rt_index_set` and `rt_push` now store through `spl_core_store_element`.
  It decodes a tagged int, a wide box or a u64 box to the raw element, the
  twin of Rust's `value.as_int()`. `rt_array_set` / `rt_array_push` are
  unchanged.

## 3. Typed `[u64]` `for` loop decoded raw words (JIT + native) — FIXED (seed)

- `for y in w` with `w: [u64] = [56, 8, 255]` summed 263 (56 became 7, 8
  became 1). The seed lowering (`mir/lower/lowering_stmt.rs`,
  `iterable_is_array`) emits `rt_array_get` + `UnboxInt`. The JIT's inline
  `rt_array_get` (`codegen/instr/calls.rs` `compile_inline_array_get`) tags
  BYTES but returns U64_PACKED words raw, and the C `rt_array_get` returns raw
  for both layouts.
- Fix: a typed `[u64]` iterable reads with `rt_typed_words_u64_at`, the
  accessor `a[i]` already uses, and skips the unbox. Typed `[u8]` and untyped
  loops are unchanged.
- Self-hosted compiler: `lower_for_array_indexed`
  (`src/compiler/50.mir/mir_lowering_stmts.spl`) has the same `[u8]` defect.
  The fix (read through `rt_bytes_u8_at` + cast, mirroring `expr_dispatch.spl`
  `typed_u8_runtime_read`) is split out to branch
  `work/selfhost-forloop-packed-u8`. It will land with a Stage 2 proof,
  because Stage 2 compiles that file natively and the fix has not been
  exercised. `[u64]` has no self-hosted index-read precedent and is still
  open.
- Still open: seed array destructuring (`val [p, q] = data`,
  `lowering_stmt.rs:117`) fails codegen in JIT and native with
  `GlobalLoad: unresolved identifier 'p'`. That has to be fixed before its
  `rt_array_get` + `unbox_u64` element read can be tested.

## 4. Wide integers compared, hashed and ordered by address (C + Rust) — FIXED

- C `rt_native_eq` / `rt_core_value_eq_inner`: two wide boxes of the same
  value were unequal, and a wide box never equalled a u64 box of the same
  value. Fix: `spl_core_heap_int_eq`. It makes one registry probe per side,
  the same count as the uint-only test it replaces.
- C `rt_core_dict_hash` hashed a wide box by address. It now hashes by value,
  exactly like the u64 box.
- C `rt_sort_cmp` ranked heap ints Equal, so `max` and `sort` of values
  >= 2^60 kept the input order. It now orders tagged, wide and u64 values
  numerically, with negative < unsigned. C `rt_array_max` on a packed array
  compares the raw elements unsigned (u64::MAX is the max).
- Rust `value_hash` hashed `HeapInt` by address (JIT dict miss). The
  UInt-vs-signed equality arm accepted only inline ints. Both are now by value.
- Still open: `d[k] = v` boxes a typed-`u64` key with `rt_value_u64`, but
  `d.contains_key(k)` passes the raw word. The same key misses (JIT and
  native) for k >= 2^60. That is MIR key boxing, not array code.

## 5. `any` / `all` / untyped `index_of` leaked raw results — FIXED

- `rt_array_any` / `rt_array_all` return a raw 0/1 and `rt_index_of` a raw
  i64 in both lanes. HIR typed the call ANY (`hir/lower/expr/mod.rs`): the
  untyped-receiver table had no entry for these methods, and the typed-array
  table had none for `any`/`all`. With no conversion, `print` showed `nil`,
  `0` or `<value:0x1>`.
- Fix: `any`/`all` are typed BOOL (both tables), and untyped `index_of` is
  typed I64. The JIT also missed on `[u8]` (`idx=-1`) because Rust
  `rt_array_index_of` read the packed buffer as slots (see 6).

## 6. Rust runtime + interpreter on packed arrays (`[u8]` max/sorted…) — FIXED

- Rust `collections.rs`: `reverse`, `reversed`, `sorted`, `fill`, `min`,
  `max`, `sum`, `count`, `index_of`, `last_index_of`, `filter`, `find`,
  `enumerate`, `flatten`, `unique`, `take`, `drop`, `join`,
  `all_truthy`/`any_truthy`, `zip` and `rt_contains` all used `as_slice()`
  on packed arrays. That reads past a `[u8]` buffer and misreads words. The
  JIT printed heap addresses for `sorted` and 231 for `max`.
- Fix: `RuntimeArray::element_at(i)` / `elements()` (a lazy per-index
  iterator, with early exit and nothing materialised) read packed elements
  at their own width. `index_of`/`last_index_of`/`count`/`contains`/`sum`/
  `all_truthy`/`any_truthy` scan the raw slots of a packed array: the needle
  is decoded once, so no element is boxed. A first draft collected a tagged
  copy per call, which cost 395 MB RSS / 4.0 s on the contains/index_of
  probe; the lazy version costs 44.7 MB / 0.17 s. Base was 42 MB / 1.9 s
  and gave wrong answers. `reversed`/`sorted` copy and keep
  the packed layout. `reverse` reverses the raw buffer at element width.
  `min`/`max` compare packed elements unsigned and order heap ints by value.
- Interpreter (`interpreter_method/collections.rs`): `sort`, `sort_desc`,
  `sorted`, `min` and `max` ranked `Value::UInt` Equal, so `max` returned the
  last element and `sorted` the input order. They now fall back to
  `numeric_ordering`.
- Still open (interpreter): `t = t + x` with `t: i64` and `x: u8` wraps at
  256. `interpreter/expr/ops.rs` gives a mixed Int/UInt op the unsigned width
  by design, while the compiled lanes promote. That is a language-semantics
  decision, so it is recorded here and not changed.

## 7. JIT corrupted a copied `[u8]` after `reverse` — FIXED (same as 6)

- `var b = a.copy(); b.reverse()` printed `[98, 111, 111, 108]` ("bool").
  `var d = a; d.reverse()` then SIGSEGV'd. Rust `rt_array_reverse` swapped
  8-byte slots over a 4-byte buffer, which is heap corruption. `pop` was
  already layout-aware. This is not the hoisted-read defect
  (`jit_hoisted_u8_data_ptr_ignores_slot_layout_2026-10-19.md`): it is a
  mutating op, `collections.rs` `rt_array_reverse` only.

## 8. Float read from a mixed literal into `f64` — RECORDED

- `[1.5, 2.25]`, `xs.push(1.5)`, and untyped params all round-trip correctly
  in all three engines.
- `val m = [1, 2.5]; val h: f64 = m[1]` prints a denormal (heap-box address
  bits) in JIT and native; the interpreter prints 2.5. HIR types an array
  literal from its FIRST element (`hir/lower/expr/collections.rs`
  `lower_array`, `hir/lower/expr/inference.rs` `Expr::Array`), so the
  literal is `[i64]`. `m[1]` then lowers to `UnboxInt`, which passes the
  float box through, and the store into the `f64` local reinterprets the
  handle bits. The fix is element-type unification for mixed numeric
  literals (or ANY). That changes type inference for every literal, which is
  beyond this lane.

## 9. Untyped `push` of a typed int is not boxed (JIT + native) — RECORDED (found while measuring)

- `fn fill(data, n): ... data.push(i % 251)` (`i` is an inferred i64) lowers
  to `MethodCallStatic push args: [raw i64]` with no `BoxInt`. The raw word is
  stored as if it were a RuntimeValue, so an element whose low 3 bits are 0
  decodes `>> 3`, and others print `<value:0xf6>`. For 1000 pushes the
  interpreter sums 124506, while JIT and native sum 110719. The same push on a
  local `var h = []` is correct. It is identical on base. Fix site: argument
  boxing for dynamic (ANY-receiver) builtin method calls in the seed MIR
  method lowering (`mir/lower/lowering_expr_method.rs`), like
  `box_arg_for_any_param` already does for dict keys. Not changed here,
  because it affects every untyped method call.

## 10. Generic-layout `[u64]` holding words >= 2^60 (JIT + native) — RECORDED (identical on base)

- `var w: [u64] = []; w.push(1152921504606846981u64)` is a generic (non-packed)
  array. The interpreter prints `w[0]=1152921504606846981`. JIT and native
  print `17293822569102704645` (the same bits plus `0xE000000000000000`, a
  sign-extended inline box) on both base and this branch. `for y in w` takes
  the `rt_for_iterable` path there, not the fixed typed loop. Rust
  `rt_typed_words_u64_at` returns `to_raw()` for a heap box in a generic slot,
  where C uses `rt_value_as_u64`. The writer side (`rt_typed_words_u64_push`
  on a generic array) has to be audited together with it.
- An untyped `data.push(v)` with `v: u64 = 2^64 - 2` reads back garbage in
  JIT and native (base too). The cause is the same as 9: the argument is not
  boxed. Rust `rt_array_set`/`rt_array_push` U64 arms decode with `as_int()`,
  which knows `HeapInt` but not `HeapUInt`. The C twin
  (`spl_core_packed_element_arg`) also decodes u64 boxes. That is a known
  write-side divergence.

## Follow-ups (pre-existing, not changed here)

- C hashes a small (< 2^60) u64 box as `value ^ 0x55494e545f553634`, but an
  equal inline int hashes as its raw word. Dict paths canonicalise a small u64
  box to an inline int first (`rt_core_dict_canon`), so dict lookups agree.
  Any other caller of `rt_core_dict_hash` on an uncanonicalised key would
  not. Rust normalises inside `value_hash` (`equality.rs` UInt arm).
- `data.any(\x: x)` / an Option-returning predicate on an untyped receiver
  is wrong in JIT and native, on base (non-bool garbage) and here (a bool
  that does not track truthiness). The closure returns a raw value, and the
  runtime tests RuntimeValue truthiness on it.
- Untyped `any`/`all` are typed BOOL only when their one argument is
  callable: a lambda, a placeholder, or an expression of `HirType::Function`
  type such as a named function. A closure held in a variable
  (`val p = \x: x > 0; data.all(p)`) is still HIR-typed ANY, so JIT/native
  print `nil` / `<value:0x1>` (same as base). Boxing the raw result at the
  codegen dispatch sites (`codegen/instr/calls.rs`,
  `closures_structs.rs`, `llvm/emitter.rs`, `llvm/functions.rs`) is NOT safe
  as things stand. `MethodCallStatic` carries no result type and
  `build_vreg_types` assigns it none, so codegen cannot tell a BOOL-typed
  call from an ANY-typed one. When the call is BOOL-typed, MIR already
  applies `rt_value_bool` to the raw word, and a tagged false (19) is
  nonzero, so it would read as true. The fix is to carry the result type on
  `MethodCallStatic` (or type the closure local as `Function`), then box at
  dispatch.
- A user method `fn any(f)` that takes a callable argument and returns a
  non-bool is forced to BOOL when reached through an untyped receiver. This
  is the remaining cost of the gate.
- Typed `[i64].any/.all` in a loop (JIT) now gives the right count (400 vs 0
  on base) at the same time (0.29-0.32 s), but max RSS is a constant
  ~2-3 MB higher (42.0 -> 44.6-45.0 MB). It does not grow with the iteration
  count (200 vs 2000 rounds), so it is not a per-call leak. Native: 0.94 s,
  3224 vs 3236 KB.
- With a user class that defines `any`, an untyped `data.any(\x: ...)` on an
  ARRAY in the same program dispatches to the user method in the JIT
  (name-based recovery). That is why `user_method_named_any_all.spl` is a
  separate fixture.
- `collection_req002_any_all_shortcircuit.spl`: the interpreter returns 1
  (base and here). JIT and native now return 0 and print the OK line (they
  returned 1 on base).

## Tests

- `src/runtime/test/rt_array_hardening_selfcheck.c` covers 1, 2 and 4 (53
  `CHECK` sites, 65 evaluations). It is red on base: ASan heap-buffer-overflow in `rt_string_join`.
- `runtime/src/value/collection_tests.rs` `packed_array_hardening` covers 4,
  6 and 7 (3 tests, all red on base).
- `test/fixtures/engine_differential/packed_array_hardening.spl` plus the
  driver test
  `native_untyped_packed_index_parity.rs::packed_array_hardening_fixture_agrees_across_engines`:
  interpreter == JIT == native.

## Byte order

Every packed read and write that was touched reads at the element's own width
(`uint8_t*` / `uint64_t*`, `&[u8]` / `&[u64]`), or converts at the value
level. No byte buffer is reinterpreted as words or the other way round. Copies
that keep the layout (`rt_array_copy`) are same-layout memcpy. No big-endian
user-mode emulator is installed on this host (no `/usr/bin/qemu-*`), so the
tests pin every element numerically against the raw buffer instead.
