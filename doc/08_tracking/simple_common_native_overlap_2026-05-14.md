# Simple/Common Native Overlap Inventory - 2026-05-14

Purpose: track common-library surfaces that exist in both native Rust/C runtime
code and pure Simple code, then route performance work through reusable Simple
optimization providers rather than delegating common algorithms back to Rust/C.

## Current Overlap

| Area | Native/Rust/C surface | Pure Simple surface | Optimization-plugin focus |
|------|------------------------|---------------------|----------------------------|
| Array/list runtime | `src/compiler_rust/runtime/src/value/collections.rs`, `src/compiler_rust/compiler/src/interpreter_method/collections.rs`, `src/compiler_rust/compiler/src/codegen/instr/collections.rs` | `src/compiler_rust/lib/std/src/core/list.spl`, `src/lib/common/pure/list.spl`, `src/lib/gc_async_mut/array.spl`, `src/lib/nogc_sync_mut/array.spl`, `src/lib/nogc_async_mut/array.spl` | Bounds/index facts, push capacity growth, fixed-size buffer lowering, `len`/index inline lowering |
| Hash map / dict | `src/compiler_rust/runtime/src/value/dict.rs`, `src/compiler_rust/runtime/src/value/hpcollections/hashmap.rs`, `src/compiler_rust/compiler/src/interpreter_extern/collections/collections_hashmap.rs` | `src/compiler_rust/lib/std/src/collections/hashmap.spl`, `src/lib/common/map/*.spl`, `src/lib/*/src/map.spl`, `src/lib/*/src/collections/hashmap.spl` | Hash/key probe loop CSE, table capacity hints, key equality specialization, iterator allocation removal |
| Hash set / set utils | `src/compiler_rust/runtime/src/value/hpcollections/hashset.rs`, `src/compiler_rust/compiler/src/interpreter_extern/collections/collections_hashset.rs` | `src/compiler_rust/lib/std/src/collections/hashset.spl`, `src/compiler_rust/lib/std/src/core/set.spl`, `src/lib/common/set_utils*.spl`, `src/lib/*/src/set.spl` | Membership test specialization, duplicate insert fast path, loop-invariant hash hoisting |
| B-tree / ordered collections | `src/compiler_rust/runtime/src/value/hpcollections/btreemap.rs`, `src/compiler_rust/runtime/src/value/hpcollections/btreeset.rs`, `src/compiler_rust/compiler/src/interpreter_extern/collections/collections_btreemap.rs`, `collections_btreeset.rs` | `src/compiler_rust/lib/std/src/collections/btreemap.spl`, `btreeset.spl`, `src/lib/common/b_tree/traverse.spl`, `src/lib/common/tree/*.spl`, `src/lib/*/src/collections/btree.spl` | Node traversal inlining, comparison hoisting, range iterator allocation removal |
| Traversal / graphs | `src/compiler_rust/dependency_tracker/src/graph.rs`, `src/compiler_rust/compiler/src/linker/analysis/graph.rs` | `src/compiler_rust/lib/std/src/core/graph.spl`, `src/compiler_rust/lib/std/src/tooling/compiler/graph_utils.spl`, `src/lib/common/graph/*.spl`, `src/lib/*/dependency_tracker/graph.spl` | Worklist queue specialization, visited-set specialization, recursion-to-loop lowering where safe |
| Concurrent collections | `src/compiler_rust/runtime/src/concurrent/{queue,map,stack}.rs`, `src/compiler_rust/runtime/src/value/ffi/concurrent/{queue,map,stack}.rs` | `src/lib/nogc_async_mut/concurrent/collections.spl`, `src/lib/nogc_async_mut_noalloc/collections/*.spl` | Atomic/CAS intrinsic lowering, ring-buffer modulo masks, noalloc fixed-capacity bounds proof |
| String / bytes | `src/compiler_rust/runtime/src/value/collections.rs`, `src/compiler_rust/parser/src/lexer/strings.rs`, `src/os/libc/include/string.h` | `src/compiler_rust/lib/std/src/core/string*.spl`, `src/lib/common/string_core.spl`, `src/lib/string_core.spl`, `src/lib/*/io/string_helpers.spl` | Direct byte load/store lowering, string length inline lowering, builder append fusion |

## 2026-05-14 Optimizer Slice

- `simple.opt.math.strength_reduce` now covers additional small multiplies:
  `11`, `13`, `17`, and `31`.
- This directly supports overlap hot paths such as bit packing (`* 11`),
  packed-field sizing (`* 13`), nibble/color expansion (`* 17`), and byte
  mixing (`* 31`) without requiring Rust/C helpers.
- `collection_opt` now exposes a dedicated hot-path provider,
  `simple.opt.collection.loop_access`, instead of inheriting generic MIR
  provider metadata. Its contract requires `typed_mir`, `loop_bounds`, and
  `collection_layout`, and advertises `canonical_collection_loops`,
  `hoisted_collection_queries`, and `append_fusion`.
- The first `simple.opt.collection.loop_access` rewrite is implemented:
  repeated typed collection length calls such as `rt_array_len` in one MIR
  block are canonicalized when the duplicate result is used only by the
  adjacent bounds check. The bounds checks stay explicit, but the redundant
  helper dispatch is removed from hot indexed traversal blocks.
- The same provider now also handles traversal-compare shapes: when a duplicate
  typed collection length query has one immediate consumer that is not a
  recognized bounds check, the pass replaces the duplicate runtime call with a
  local copy from the canonical length. This keeps list/set/map traversal loops
  from redispatching `rt_array_len`/`rt_string_len`/`rt_dict_len` in adjacent
  compare or guard instructions.
- Set membership queries now participate in the same pure-query hoisting lane:
  `contains` is treated like `contains_key` for loop-invariant collection
  calls, while mutating operations such as `insert` remain non-hoistable.
- Same-block duplicate pure collection queries are now canonicalized until a
  possible collection mutation appears. Repeated read-only `contains`,
  `contains_key`, `get`, `first`, `last`, `len`, and `is_empty` dispatches over
  the same operands reuse the first result; mutating calls such as `insert`
  clear the reuse window.
- Typed collection length canonicalization now also removes duplicate
  `rt_array_len`/`rt_string_len`/`rt_dict_len` calls when the duplicate result
  has multiple consumers, by replacing the duplicate runtime dispatch with a
  local copy from the canonical length. Mutating collection calls fence the
  reuse window so traversal guards do not keep stale lengths after `push`,
  `insert`, or other state-changing operations.
- `src/lib/common/hash/adler32.spl` now uses the same pure Simple chunked
  Adler-32 path as the OS crypto module: 8-byte typed loads, deferred modular
  reduction, and strength-reduced `_adler_reduce` instead of per-byte `%`
  reduction. This keeps the common `std.hash.adler32` surface aligned with the
  optimized pure Simple implementation.
- The OS and common Adler-32 paths were then narrowed to 4-byte typed loads
  after native benchmarking showed that the smaller chunk reduces generated
  code overhead while preserving the same deferred-reduction algorithm.
- The crypto pattern provider now recognizes `os.crypto.crc32.update_byte`,
  `update_u32`, and `update_u64` as the same CRC32 idiom family as
  `std.common.crypto.crc32.*`, so OS pure Simple CRC wrappers can reach the
  existing target-gated CRC intrinsic rewrite path.
- Verified with `SIMPLE_LIB=src bin/release/x86_64-unknown-linux-gnu/simple
  test test/unit/compiler/mir_opt/strength_reduction_spec.spl
  --mode=interpreter --clean` passing 14 examples.
- Verified with `SIMPLE_LIB=src bin/release/x86_64-unknown-linux-gnu/simple
  test test/unit/compiler/mir_opt/pass_descriptor_spec.spl
  --mode=interpreter --clean` passing 7 examples.
- Verified with `SIMPLE_LIB=src bin/release/x86_64-unknown-linux-gnu/simple
  test test/unit/compiler/mir_opt/collection_opt_spec.spl
  --mode=interpreter --clean` passing 7 examples.
- Verified with `SIMPLE_LIB=src bin/release/x86_64-unknown-linux-gnu/simple
  test test/unit/lib/common/hash/adler32_spec.spl
  --mode=interpreter --clean` passing 11 examples.
- Latest one-sample port benchmark with `SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c`
  kept checksum parity. Pure Simple beat C/Rust for XXHash64 (`1.73x` C,
  `1.57x` Rust) and ChaCha20 (`1.22x` C, `1.06x` Rust), but still missed parity
  for CRC32 (`0.78x` C, `0.88x` Rust) and Adler32 (`0.91x` C, `0.94x` Rust).
- Latest three-sample median after the 4-byte Adler change kept checksum parity:
  CRC32 remains below parity (`0.78x` C, `0.79x` Rust); Adler32 improved but
  still narrowly misses parity (`0.94x` C, `0.99x` Rust).
- Provider coverage for OS CRC aliases is verified in the cipher pattern engine
  and parity specs, but the port benchmark still needs a CRC loop shape that
  exposes `update_u64`/`update_u32` calls to the pattern pass before this can
  close the measured CRC32 throughput gap.
- A dedicated collection parity benchmark now exists at
  `test/perf/collections/run_collection_benchmarks.shs`. Its first
  one-sample run with `SIMPLE_NATIVE_RUNTIME_BUNDLE=core-c` kept checksum
  parity for `list_traverse`, `list_push`, and `set_contains`, but showed the
  remaining optimizer gap clearly: list traversal was `0.00x` C/Rust
  (`16,492` Simple ops/ms vs `4,773,197` C and `6,904,987` Rust), list push was
  `0.01x` C / `0.02x` Rust, and set-like linear membership was still `0.00x`
  C/Rust. This benchmark is intentionally a gate for future collection
  optimizer work rather than proof of parity.
- The Simple `collection_opt` pass now has a conservative typed-array index
  specialization rule: `rt_index_get(array, idx)` is rewritten to
  `rt_array_get(array, idx)` only when MIR local metadata proves the receiver is
  an `Array`. This locks the intended pure Simple optimizer behavior even
  though the current benchmark path still uses the Rust-hosted lowering.
- The Rust-hosted lowering/runtime path used by native benchmarks now has
  `[u64]` typed word helpers matching the prior `[u32]` lane:
  `rt_typed_words_u64_at`, `rt_typed_words_u64_push`, and
  `rt_typed_words_u64_set`. Rebuilt native output for
  `collection_simple.spl` removed the previous hot-loop `rt_index_get` calls.
  A one-sample rerun kept checksum parity and improved Simple throughput, but
  parity remains far away: list traversal rose to `20,282` ops/ms, list push to
  `24,157` ops/ms, and set-like linear membership to `34` ops/ms versus C/Rust
  results in the millions for traversal/push and thousands for membership.
  The remaining cost is typed helper call/check overhead inside the element
  loop, not generic index dispatch.
- The active Cranelift native path now inlines `rt_typed_words_u64_at` using
  the same slot representation rules as the runtime helper: bounds are still
  checked, integer slots are untagged, and non-int raw values are preserved.
  The existing `[u32]` typed-word read inliner was generalized to the same
  helper, and LLVM received the matching inactive-backend fix. Disassembly of
  `collection_simple.spl` now shows direct slot loads in the list traversal
  loop instead of per-element typed-word calls. A one-sample benchmark with the
  isolated rebuilt driver kept checksum parity and measured list traversal at
  `585,796` Simple ops/ms (`0.10x` C, `0.09x` Rust), list push at `21,375`
  Simple ops/ms, and set-like linear membership at `340` Simple ops/ms. The
  next measured gap is push growth/append lowering and primitive equality in
  membership scans.
- Typed word runtime reads now stamp primitive vreg result types, and equality
  over proven primitive scalars lowers to native integer compare instead of
  redispatching through `rt_native_eq`/`rt_native_neq`. Disassembly of
  `collection_simple.spl` shows no `rt_native_eq` call in `set_contains`, and a
  one-sample rerun kept checksum parity while improving set-like membership to
  `1,126` Simple ops/ms (`0.17x` C, `0.09x` Rust). The remaining collection
  gap is still substantial: list traversal measured `532,769` Simple ops/ms
  (`0.09x` C, `0.06x` Rust), and list push remains dominated by append/growth
  overhead at `21,542` Simple ops/ms.

## Next Concrete Plugin Work

1. Extend `simple.opt.collection.loop_access` from duplicate length
   canonicalization and typed dispatch selection to full `len`-guarded
   array/list loops so indexed traversal over `[u8]`, `[u32]`, `[u64]`, and
   fixed arrays emits one bounds proof per loop and lowers element access to an
   unchecked/direct load instead of a per-element helper call.
2. Add duplicate map/set probe-loop specialization for primitive-key
   `contains`, `contains_key`, and `get` calls after MIR exposes the hash/probe
   internals rather than only opaque runtime calls.
3. Add static-table materialization for pure Simple `[u8]` and `[u32]` literals
   after resolving `native_u8_array_literal_not_packed_2026-05-13.md`.
4. Benchmark primitive list/set/map traversal against the Rust hpcollection
   extern surfaces before removing native shortcuts.
