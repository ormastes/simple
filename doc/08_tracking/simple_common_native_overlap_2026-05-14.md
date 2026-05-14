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
- Verified with `SIMPLE_LIB=src bin/release/x86_64-unknown-linux-gnu/simple
  test test/unit/compiler/mir_opt/strength_reduction_spec.spl
  --mode=interpreter --clean` passing 14 examples.
- Verified with `SIMPLE_LIB=src bin/release/x86_64-unknown-linux-gnu/simple
  test test/unit/compiler/mir_opt/pass_descriptor_spec.spl
  --mode=interpreter --clean` passing 7 examples.

## Next Concrete Plugin Work

1. Implement the `simple.opt.collection.loop_access` rules for `len`-guarded
   array/list loops so indexed traversal over `[u8]`, `[u32]`, and fixed arrays
   emits one bounds proof per loop instead of repeated helper dispatch.
2. Add static-table materialization for pure Simple `[u8]` and `[u32]` literals
   after resolving `native_u8_array_literal_not_packed_2026-05-13.md`.
3. Add map/set probe-loop specialization for pure Simple `contains`, `insert`,
   and `get` on primitive keys, then benchmark against the Rust hpcollection
   extern surfaces before removing native shortcuts.
