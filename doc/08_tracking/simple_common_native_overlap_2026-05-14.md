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
- Typed word pushes now have the same conservative inline fast path as typed
  byte pushes: when the array is slot-backed and has spare capacity, Cranelift
  stores the tagged word and bumps `len` directly; capacity misses and
  byte-packed arrays still fall back to the runtime grow helper. Disassembly of
  `bench_list_push` shows the fast store in the loop with the helper call only
  on the fallback branch. A one-sample rerun kept checksum parity and improved
  list push to `135,428` Simple ops/ms (`0.04x` C, `0.09x` Rust); traversal was
  `576,292` Simple ops/ms (`0.10x` C, `0.06x` Rust), and set-like membership
  was `1,194` Simple ops/ms (`0.19x` C, `0.12x` Rust).
- Typed word reads now use the vreg signedness map for their index operand:
  unsigned indices skip negative-index normalization and lower bounds to a
  single unsigned `index < len` check, while signed or unknown indices keep the
  existing negative-index semantics. Disassembly of `bench_list_traverse`
  removed the prior `cmovl`/signed-normalization sequence from the element
  loop. A one-sample benchmark kept checksum parity and measured list traversal
  at `907,554` Simple ops/ms (`0.28x` C, `0.15x` Rust), list push at `133,212`
  Simple ops/ms (`0.06x` C, `0.09x` Rust), and set-like membership at `1,858`
  Simple ops/ms (`0.27x` C, `0.14x` Rust).
- Compiler-generated typed word reads now also trust the typed array lane for
  slot representation: `[u32]`/`[u64]` reads untag the stored integer directly,
  while generic or mixed arrays still route through `rt_index_get`. The
  traversal hot loop now shows only an unsigned bound check, slot load, and
  shift for element access. A one-sample benchmark kept checksum parity and
  measured list traversal at `932,410` Simple ops/ms (`0.23x` C, `0.10x`
  Rust), list push at `121,840` Simple ops/ms (`0.04x` C, `0.08x` Rust), and
  set-like membership at `1,882` Simple ops/ms (`0.27x` C, `0.15x` Rust).
- Compiler-generated typed word pushes now also trust the slot-backed typed
  array lane: the fast branch checks only `len < capacity`, stores the tagged
  word, and bumps `len`; capacity misses still fall back to the runtime helper.
  Disassembly of `bench_list_push` shows the byte-packed flag load/test is gone
  from the typed word append loop. A one-sample benchmark kept checksum parity
  and measured list traversal at `1,171,843` Simple ops/ms (`0.25x` C, `0.12x`
  Rust), list push at `129,398` Simple ops/ms (`0.04x` C, `0.09x` Rust), and
  set-like membership at `2,448` Simple ops/ms (`0.35x` C, `0.18x` Rust).
- Pure Simple collection benchmarks now use the existing capacity constructor
  for list construction, matching the C `malloc(size)` and Rust
  `Vec::with_capacity` reference setup, and hot loop bounds are cached in local
  values instead of repeatedly calling tiny size helpers. Typed array
  `.push(...)` expression statements now lower to MIR calls with `dest: None`,
  and the Cranelift typed-word push inliner skips bool-result block plumbing
  when that result is ignored. A one-sample benchmark with checksum parity
  measured list traversal at `1,237,072` Simple ops/ms (`0.34x` C, `0.19x`
  Rust), list push at `144,527` Simple ops/ms (`0.05x` C, `0.10x` Rust), and
  set-like membership at `1,721` Simple ops/ms (`0.26x` C, `0.13x` Rust).
  The same ignored-result codegen path also applies to typed byte pushes, so
  `[u8]` push statements avoid unused bool-result plumbing on both packed and
  slot-backed fast branches.
- HIR lowering now carries a narrow loop proof for `while index < length` when
  `length` is a cached `array.len()` local and `index` is unsigned. Matching
  typed `[u8]`, `[u32]`, and `[u64]` reads inside the loop lower to unchecked
  typed-read intrinsics; the Cranelift typed-word unchecked inliner emits only
  the data-pointer load, indexed slot load, and tag shift. Disassembly of
  `bench_list_traverse` and `set_contains` shows no per-element typed-word
  bounds branch and no runtime equality call in the hot scan. A one-sample
  benchmark kept checksum parity and measured list traversal at `1,259,325`
  Simple ops/ms (`0.22x` C, `0.20x` Rust), list push at `144,183` Simple
  ops/ms (`0.05x` C, `0.10x` Rust), and set-like membership at `2,000` Simple
  ops/ms (`0.31x` C, `0.15x` Rust).
- The same loop proof now hoists typed-array data pointers for read-only
  guarded loops. The lowering rejects loop bodies that assign, index-mutate, or
  pass the array to escaping calls, then emits `rt_array_data_ptr` once before
  the loop body and uses `*_data_at` typed-read intrinsics inside the hot scan.
  Disassembly of `set_contains` shows the `0x18` data-pointer load before the
  scan loop, and `bench_list_traverse` performs that load once per traversal
  pass instead of once per element. A one-sample benchmark kept checksum parity
  and measured list traversal at `1,236,787` Simple ops/ms (`0.29x` C, `0.21x`
  Rust), list push at `136,519` Simple ops/ms (`0.04x` C, `0.09x` Rust), and
  set-like membership at `2,321` Simple ops/ms (`0.36x` C, `0.18x` Rust).
- Fresh-capacity typed append loops now have a separate proof for
  `array = rt_array_new_with_cap(length)` followed by
  `while unsigned_index < length` with exactly one non-escaping typed push in
  the loop body. Those pushes lower to `*_push_known_data_at`, hoisting the
  array data pointer and avoiding the generic append capacity/grow branch.
  The length update is deferred to loop exit for this strict shape, so
  disassembly of `bench_list_push` shows the hot loop storing directly through
  the hoisted data pointer without a per-element header write. A one-sample
  benchmark kept checksum parity and measured list traversal at `1,550,495`
  Simple ops/ms (`0.45x` C, `0.16x` Rust), list push at `144,868` Simple
  ops/ms (`0.04x` C, `0.10x` Rust), and set-like membership at `2,007` Simple
  ops/ms (`0.28x` C, `0.15x` Rust). The remaining push gap is now dominated by
  loop/allocation/codegen overhead rather than capacity, grow dispatch, or
  per-element length updates in the hot append body.
- `rt_array_new_with_cap*` now matches C `malloc` and Rust
  `Vec::with_capacity` setup more closely by allocating uninitialized element
  capacity with length `0`; the existing `rt_array_new` path keeps zero-filled
  storage for generic callers. The strict append proof writes slots before
  publishing length, so the benchmark path no longer pays to zero slots it will
  immediately overwrite. A one-sample benchmark kept checksum parity and
  measured list traversal at `1,627,370` Simple ops/ms (`0.37x` C, `0.26x`
  Rust), list push at `148,731` Simple ops/ms (`0.06x` C, `0.10x` Rust), and
  set-like membership at `2,002` Simple ops/ms (`0.30x` C, `0.15x` Rust).
- MIR lowering now eliminates arrays whose only observable use is an ignored
  `push` into a capacity-allocated local. Push arguments are still lowered for
  side effects, but the dead array allocation and stores are removed. This
  matches the native compilers' ability to remove dead append-only storage in
  the synthetic push benchmark without changing checksum behavior. Disassembly
  of `bench_list_push` shows no capacity allocation call in the timed loop and
  no slot store in the inner loop. A one-sample benchmark kept checksum parity
  and measured list traversal at `1,917,783` Simple ops/ms (`0.44x` C, `0.20x`
  Rust), list push at `1,292,198` Simple ops/ms (`0.41x` C, `0.87x` Rust), and
  set-like membership at `3,534` Simple ops/ms (`0.51x` C, `0.28x` Rust).
- The pure Simple `collection_opt` provider now mirrors that MIR-level dead
  append-only capacity-array rule for already-lowered MIR: a
  `rt_array_new_with_cap*` result is removed when its only uses are ignored
  append calls, and observed append results keep the array live. This narrows
  the Rust-hosted vs pure Simple optimizer gap for synthetic list-push loops.
- The same pure Simple provider now also treats runtime collection read helpers
  (`rt_array_get` and typed word read helpers) as same-block pure queries for
  CSE until a possible collection mutation appears. This removes duplicated
  list/set read dispatches in already-lowered MIR without changing runtime
  representation or hoisting reads across append/write calls.
- Runtime array data/header pointer helpers now share the same pure-query lane,
  so repeated `rt_array_data_ptr`/`rt_array_header_ptr` reads in one mutation-free
  MIR block reuse the first pointer result. This supports pure Simple scan
  lowering patterns that materialize data pointers before indexed reads.
- Runtime array first/last and dict get/contains helpers are now included in
  the same mutation-fenced pure-query lane, covering repeated list endpoint
  reads and map/set lookups in already-lowered MIR.
- The collection optimizer provider contract now advertises
  `runtime_collection_read_cse` as a produced fact, so planner/tooling surfaces
  can distinguish this read-dispatch reuse from loop canonicalization and append
  fusion.
- Runtime collection length helpers now participate in the same non-mutating
  read window as element/data/dict helpers, so `rt_array_len`/`rt_string_len`/
  `rt_dict_len` no longer fence repeated runtime read reuse in already-lowered
  MIR.
- The pure collection hoister now also moves invariant runtime metadata reads
  (`rt_array_len`, `rt_string_len`, `rt_dict_len`, `rt_array_data_ptr`,
  `rt_array_header_ptr`) out of read-only loops, while keeping them inside loops
  that may mutate collection state.
- The pure collection hoister now also moves conservative loop-invariant scalar
  operations used by collection hot paths, including bitwise masks, shifts,
  comparisons, unary ops, casts, and bitcasts. This gives already-lowered MIR a
  pure-Simple optimization lane for repeated tag/mask work in list/set scans
  without relying on Rust/C helper rewrites.
- A fresh one-sample collection benchmark after the pure optimizer CSE commits
  kept checksum parity, but the native benchmark path still misses C/Rust
  throughput parity: list traversal measured `1,651,751` Simple ops/ms
  (`0.28x` C, `0.17x` Rust), list push measured `1,190,841` Simple ops/ms
  (`0.36x` C, `0.79x` Rust), and set-like linear membership measured `3,360`
  Simple ops/ms (`0.50x` C, `0.26x` Rust). The pure optimizer updates are
  therefore correctness/parity coverage for already-lowered MIR, not proof that
  the Rust-hosted native benchmark path has reached performance parity.
- A refreshed one-sample collection benchmark after adding length helpers to
  the pure runtime-read CSE window kept checksum parity and measured
  `1,550,332` Simple ops/ms for list traversal (`0.27x` C, `0.16x` Rust),
  `1,272,955` Simple ops/ms for list push (`0.44x` C, `0.85x` Rust), and
  `3,597` Simple ops/ms for set-like membership (`0.55x` C, `0.27x` Rust).
  The next native-path optimization target remains traversal/set scan loop
  overhead rather than synthetic push dead-store elimination.
- A one-sample collection benchmark after adding pure scalar LICM coverage kept
  checksum parity and measured `1,555,668` Simple ops/ms for list traversal
  (`0.27x` C, `0.16x` Rust), `1,313,346` Simple ops/ms for list push (`0.43x`
  C, `0.86x` Rust), and `3,676` Simple ops/ms for set-like membership
  (`0.55x` C, `0.27x` Rust). The current Rust-hosted native benchmark path
  therefore does not yet show a material throughput move from this pure-MIR
  coverage, but the optimizer contract now covers the already-lowered scalar
  tag/mask shape directly.
- The pure collection optimizer now generalizes dead fresh-capacity array
  removal from append-only writes to ignored-result write-only calls
  (`rt_array_set` and typed word `set` helpers included). Focused coverage
  keeps observed write results live. A one-sample collection benchmark after
  this pure-MIR widening kept checksum parity and measured `1,533,683`
  Simple ops/ms for list traversal (`0.35x` C, `0.16x` Rust), `1,177,293`
  Simple ops/ms for list push (`0.38x` C, `0.80x` Rust), and `3,053`
  Simple ops/ms for set-like membership (`0.48x` C, `0.24x` Rust). This is
  additional already-lowered MIR coverage, not proof that the native benchmark
  path has reached C/Rust parity.
- Rust-hosted MIR lowering now drops unused destinations from ignored-result
  typed collection writes before native codegen. Focused coverage verifies that
  a `[u64]` `arr.push(word)` expression statement lowers to
  `rt_typed_words_u64_push` with `dest: None`, letting the existing Cranelift
  inliner skip bool-result plumbing for that path. A one-sample collection
  benchmark after rebuilding the driver kept checksum parity and measured
  `1,832,889` Simple ops/ms for list traversal (`0.32x` C, `0.25x` Rust),
  `1,254,677` Simple ops/ms for list push (`0.40x` C, `0.82x` Rust), and
  `3,519` Simple ops/ms for set-like membership (`0.52x` C, `0.25x` Rust).
  Fresh emitted MIR for `bench_list_push` no longer contains an observed
  `rt_typed_words_u64_push` result, but traversal and set membership remain
  below native parity.
- Disassembly of the latest unstripped Simple benchmark shows
  `bench_list_traverse` and `set_contains` already use hoisted
  `rt_typed_words_u64_data_at` lowering with direct slot loads in the scan
  loop. The remaining measured gap is therefore loop/codegen quality and typed
  slot representation overhead, not generic `rt_index_get` dispatch or
  per-element bounds checking.
- The pure runtime `rt_string_to_float` stub is removed. `core_string.spl`
  now parses NUL-terminated Simple string storage with libc `strtod`, validates
  that only trailing whitespace remains, and tags the result through the
  `spl_f64_to_bits` primitive. Cranelift and LLVM both inline
  `spl_f64_to_bits` as an f64-to-i64 bitcast, so `simple-core` binaries do not
  need a Rust/C helper symbol for this conversion. A direct `simple-core` smoke
  compiled and ran `rt_string_to_float(" 3.5 ")` plus invalid trailing input,
  printing `float-ok`.
- The pure collection optimizer now treats typed byte reads
  (`rt_typed_bytes_u8_*` and little-endian typed-byte word reads) as collection
  runtime reads for same-block CSE, matching the existing typed-word coverage
  used by list/set scans. Its scalar LICM destination tracker also records
  `Bitcast`, so invariant tag/mask chains that pass through bitcasts can be
  hoisted as a unit. Verified with `collection_opt_spec.spl` passing 26
  examples and `pass_descriptor_spec.spl` passing 7 examples.
- Current-head collection benchmark after the provider coverage change kept
  checksum parity, but still misses the speed target: list traversal measured
  `1,378,190` Simple ops/ms (`0.28x` C, `0.20x` Rust), list push measured
  `1,173,779` Simple ops/ms (`0.40x` C, `0.80x` Rust), and set-like
  membership measured `3,472` Simple ops/ms (`0.52x` C, `0.26x` Rust).
- Rust-hosted native codegen now has a packed `[u64]` runtime lane:
  `rt_array_new_with_cap` calls returning `[u64]` lower to
  `rt_array_new_with_cap_u64`, `[u64]` literals use the packed constructor,
  generic array get/set/pop still re-box raw words, and hoisted `[u64]` scans
  use raw data-pointer reads. Stub fallback was disabled for the verification
  benchmark. Checksum parity passed, but parity is still not closed:
  list traversal measured `1,788,564` Simple ops/ms (`0.30x` C, `0.33x`
  Rust), list push measured `1,270,487` Simple ops/ms (`0.39x` C, `1.52x`
  Rust), and set-like membership measured `2,459` Simple ops/ms (`0.35x` C,
  `0.24x` Rust). Current disassembly shows tight raw-word load loops, so the
  next limiting gap is call/loop codegen quality, especially lack of inlining
  for the tiny `set_contains` helper.
- Rust-hosted Cranelift codegen now treats `rt_array_len` as a statically
  trusted array length read while keeping generic `rt_len` checked for dynamic
  values. This removes array tag/object-type prologue work from typed
  `Array.len()` hot helpers such as the pure Simple `set_contains` benchmark.
  Focused inline codegen tests passed, and a one-sample benchmark with
  `SIMPLE_NO_STUB_FALLBACK=1` kept checksum parity while measuring
  `1,827,381` Simple ops/ms for list traversal (`0.42x` C, `0.20x` Rust),
  `1,224,971` Simple ops/ms for list push (`0.42x` C, `0.86x` Rust), and
  `3,371` Simple ops/ms for set-like membership (`0.53x` C, `0.26x` Rust).
  This narrows the set-scan gap but still leaves pure Simple below C/Rust
  parity overall.
- The collection benchmark now has explicit speed-floor warnings in addition
  to checksum parity. A one-sample warn-only run with
  `SIMPLE_BIN=./src/compiler_rust/target/debug/simple` kept checksum parity and
  measured list traversal at `1,607,544` Simple ops/ms (`0.28x` C, `0.26x`
  Rust), list push at `1,825,515` Simple ops/ms (`0.66x` C, `1.27x` Rust),
  scalar set membership at `3,206` Simple ops/ms (`0.49x` C, `0.24x` Rust),
  and pure text `HashSet.contains` at `9` Simple ops/ms (`0.00x` C, `0.00x`
  Rust). The harness now emits `[collectionbench-warn]` rows for these misses
  and can be promoted to failure with `SIMPLE_COLLECTION_BENCH_ENFORCE=1` once
  the parity target is expected to hold.
- The core-C bootstrap runtime now exports the generated source-closure typed
  array helpers used by optimized pure Simple collection code:
  `rt_array_new_with_cap_u64`, `rt_array_data_ptr`,
  `rt_array_header_ptr`, `rt_array_set_len_known`,
  `rt_typed_words_u64_raw_data_at`, and
  `rt_typed_words_u64_store_known_data_at`. The same lane now also provides
  core roots for text hashing, tuple construction, enum construction, and the
  no-interpreter fallback calls. Rebuilding `collection_simple.spl` with
  `--runtime-bundle core-c-bootstrap --source src/lib --entry-closure` now
  links with zero generated stubs, and the resulting binary runs
  checksum-compatible collection benches instead of crashing. The source-closure
  binary measured pure text `HashSet.contains` at `193` ops/ms, up from the
  interpreted harness result of `9` ops/ms, but still far below C/Rust parity.
- The HIR imported-type loader now skips local export declarations when walking
  re-exported import chains, so source-closure native builds no longer emit the
  prior `empty module path` warning for `HashSet`'s local
  `export hashset_with_capacity`. A fresh core-C source-closure rebuild linked
  without generated stubs or import-type warnings, and the binary kept checksum
  parity while measuring pure text `HashSet.contains` at `190` ops/ms.
- The collection benchmark harness now has an opt-in source-closure mode:
  `SIMPLE_COLLECTION_BENCH_SOURCE_CLOSURE=1` switches the Simple leg to
  `native-build --source src/lib --entry-closure`. This exposed a core-C typed
  `[u64]` parity bug: `rt_array_new_with_cap_u64` needed to mark arrays with
  the same packed flag that Cranelift's typed-word inliners test before
  choosing raw-word stores and loads. After adding that flag, the source-closure
  benchmark passes checksum parity across list traversal, list push, scalar set
  membership, and text `HashSet.contains`. A one-sample run measured source-
  closure Simple at `1,086,082` ops/ms for list traversal (`0.27x` C,
  `0.18x` Rust), `1,221,167` for list push (`0.42x` C, `0.84x` Rust),
  `3,233` for scalar set membership (`0.50x` C, `0.25x` Rust), and `187` for
  pure text `HashSet.contains` (`0.00x` C/Rust).
- `text.char_code_at(index)` now has a native source-closure lowering through
  `rt_string_char_code_at` instead of falling through to
  `rt_function_not_found("str.char_code_at")`. This fixes the pure Simple hash
  loop route used by `HashMap._hash` and `HashSet.contains`; a direct
  source-closure probe resolves the helper, and the collection benchmark still
  keeps checksum parity. The one-sample timing remained dominated by the wider
  text `HashSet` design cost (`194` ops/ms in this noisy run), so this is an
  enabling correctness fix rather than the final parity change.
- HIR lowering now erases standalone string and typed-string expression
  statements before MIR, so triple-quoted doc comments in hot pure Simple
  methods no longer allocate strings at function entry. The source-closure
  `HashMap` text path also stores each entry hash, computes text hashes through
  `rt_hash_text` directly, reuses stored hashes on resize/probe, and compares
  text keys through the core-C `rt_string_eq` helper. A clean
  `native-build --entry-closure --runtime-bundle core-c-bootstrap` linked with
  no generated-stub warning and kept checksum parity while measuring
  `hashset_contains` at `17,328` Simple ops/ms. This is a large improvement
  over the earlier `190`-`194` ops/ms source-closure path, but it is still below
  the C/Rust parity target.
- The collection benchmark harness now accepts
  `SIMPLE_COLLECTION_BENCH_CLEAN=1` for source-closure runs, forcing
  `native-build --clean` so perf evidence is not accidentally taken from stale
  cached objects.
- A full one-sample clean source-closure harness run with
  `SIMPLE_COLLECTION_BENCH_SOURCE_CLOSURE=1 SIMPLE_COLLECTION_BENCH_CLEAN=1`
  kept checksum parity and measured Simple at `0.28x` C / `0.16x` Rust for
  list traversal, `0.65x` C / `1.28x` Rust for list push, `0.52x` C / `0.26x`
  Rust for scalar set membership, and `0.26x` C / `0.43x` Rust for text
  `HashSet.contains`. Pure Simple is therefore improved, but still not
  properly updated to Rust/C performance parity.

## Next Concrete Plugin Work

1. Extend the loop proof beyond direct `while index < cached_len` conditions to
   optimizer-level propagation across aliases, counted `for` loops, nested
   helper calls, and fixed arrays.
2. Add duplicate map/set probe-loop specialization for primitive-key
   `contains`, `contains_key`, and `get` calls after MIR exposes the hash/probe
   internals rather than only opaque runtime calls.
3. Add static-table materialization for pure Simple `[u8]` and `[u32]` literals
   after resolving `native_u8_array_literal_not_packed_2026-05-13.md`.
4. Fix native reachability for imported noalloc collection methods such as
   `FixedSet.add`, then retry primitive-key fixed-set benchmarking as the pure
   Simple candidate for hot membership parity.
5. Benchmark primitive list/set/map traversal against the Rust hpcollection
   extern surfaces before removing native shortcuts.
