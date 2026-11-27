# Packed [u8] plan (design only, 2026-10-27)

## 0. Headline finding
The packed-byte representation ALREADY EXISTS in both runtimes. The 8x waste is a
CREATION-SITE gap in the self-hosted (stage2/3) compiler, not a missing ABI.
So the recommendation is a small, mostly-compiler change, not a runtime-wide ABI change.

## 1. Current state (evidence)
C runtime (src/runtime/runtime_native.c):
- `RtCoreArray {kind, flags, reserved, transient_scope_id, len, cap, void* data}` :1454-1462.
- Flags: `RT_CORE_ARRAY_FLAG_BYTES 0x08`, `U64_PACKED 0x10`, `TUPLE 0x01` :301-302,:315. Byte arrays
  get a 1 GiB cap vs 100M tagged slots (:316-330); elem size 1 vs 8.
- `rt_byte_array_new(cap)` :9666 -> `rt_core_array_new(cap, FLAG_BYTES)`; `rt_byte_array_new_len` :9673.
- `rt_core_as_array` :2881 (validates heap tag + registry; this is the locked lookup in the perf bug).
- Flag-aware accessors exist (82 FLAG_BYTES uses): push/get/set/slice/concat/copy/join/equality
  (:5175, :5505, :5880, :6766, :7040, :7089, :10161-10307), `rt_array_is_byte_packed` :8778.
- Dual-layout typed bytes: `rt_typed_bytes_u8_push` :11023, `_u8_unchecked` :11036, `_u32_le_at` :11045,
  `_u64_le_at`/`_unchecked` :11049-11053 (8-iteration byte loop with per-byte flag test),
  `_u32_le_set`/`_u64_le_set` :11066/:11082, `rt_typed_bytes_u8_data_at` :13201. They already
  branch on FLAG_BYTES, so they work on both layouts (that is why generic arrays "work" but slowly).
- Some kernels outside this TU guess the layout (see comment :8770-8780; blend_mask_span bug).
Rust twin (src/compiler_rust/runtime/src/value/):
- `gc_flags::BYTE_PACKED = 0b1000` heap.rs:108; `is_byte_packed()` collections.rs:910;
  `rt_byte_array_new` collections.rs:1468 (sets flag :1489), `_new_len` :1499.
- Copy path memcpy for packed, generic path for tagged (collections.rs:~7098-7125, comment says
  `rt_array_repeat -> rt_array_new` gives tagged arrays for non-u8). Packing conversion helpers
  and "spawn unpacks every packed array" at :312-370 (packed arrays are unpacked at thread spawn).
Seed compiler (Rust) emission:
- Empty `[u8]` literal and typed `[u8]` decl lower to `rt_byte_array_new`:
  mir/lower/lowering_expr_collection.rs:93-132 (also u64 -> `rt_array_new_with_cap_u64`),
  mir/lower/lowering_stmt.rs:255-305, :378.
- Inline typed-bytes LE load: codegen/instr/calls.rs:3889 `compile_inline_typed_bytes_le_unchecked`,
  codegen/llvm/functions/calls.rs:2058. Symbol table: common/src/runtime_symbols.rs:140,431,155,2201.
Self-hosted compiler (src/compiler):
- grep finds `rt_byte_array_new*` ONLY in the file-write scratch buffer
  (50.mir/_MirLoweringExpr/switch_operators_calls.spl:1403). No `[u8]` literal/`[]`/typed-decl path
  selects the packed constructor, so `var buf: [u8] = []` + push gives a generic tagged array
  (FLAG_BYTES == 0) -> 8 B/elem, exactly the bug doc's `test dl, 8` observation.
  (Not verified: whether HIR->MIR for `val x: [u8] = []` has any other path; check first in PR 1.)
- Typed-bytes ops are only classified, not expanded: 60.mir_opt/mir_opt/collection_opt_core.spl:710-720.
- u8 element loads: `rt_bytes_u8_at` is used for copy loops (50.mir/mir_lowering_stmts.spl:821-885).
- A workaround tag references `native_comprehension_packed_u8_array_mir_2026_10_20`
  (10.frontend/frontend_advisory_preprocess_port_v1.spl:94): the self-hosted MIR already rejects
  some comprehensions over packed u8 arrays - a known interaction to fix in PR 2.
Bug doc: doc/08_tracking/bug/native_xxh3_40x_slower_than_runtime_perf_2026-10-27.md (in commit
9f6e090ce23; not present in the current working tree, whose branch is release/1.0.0).

## 2. Options
(a) Distinct packed kind with dual-representation accessors  [ALREADY THE STATE OF THE RUNTIME]
  + zero new rt_* symbols; accessors already branch on flag; GC/refcount unchanged (header same,
    only `data` stride differs); text<->bytes already handled (join/to_string render per-element).
  - per-access flag test; kernels in other TUs can guess wrong (:8770); mixed arrays flow across
    FFI as generic or packed unpredictably until creation is uniform.
  ABI: none new. Remaining work = make the compiler choose the constructor.
(b) Packed storage for ALL [u8] (make it the only representation)
  + no flag test, inline load `mov [p+off]` possible; simplest mental model.
  - Breaks every consumer that assumes tagged slots: every rt_* reading elements (array get/set/
    push/pop/slice/concat/sort/map/reduce/index_of/join, ~82 sites), SFFI/extern signatures taking
    `[u8]` (rt_file_write_bytes_array, sha/aes/random, engine2d masks), serialization (SMF/SDN
    blobs), thread spawn unpack, Rust interpreter values (RuntimeValue tagged ints), `any` boxing
    of elements. Needs removal of the generic u8 path in both runtimes + flag day.
(c) Separate `Bytes` type
  + clean type-level guarantee, no dynamic flag; room for slice views.
  - New stdlib type, new syntax/typing rules, migration of all `[u8]` APIs (crypto, io, net, text),
    conversion APIs; largest ABI + language surface. Not justified when (a) already exists.

## 3. Dual-implementation rule
Source: .claude/rules/vcs.md:247, :319, :353 (`push-rt-dual-implementation`, blocking, DELTA vs
the commit the push replaces); scripts/check/check-rt-dual-implementation-ratchet.shs with
baseline scripts/check/rt_dual_implementation_baseline.txt and census
scripts/check/rt-dual-implementation-census.shs. Rule: no NEW single-lane rt_* (C-only or
Rust-only); lanes are never unioned; baseline stale entries also fail.
Consequence for this plan: prefer NO new rt_* symbols (recommended option adds none). If one is
needed (e.g. `rt_array_promote_bytes`), land it in the SAME PR in C (runtime_native.c), Rust
(value/collections.rs + runtime_symbols.rs list at :140/:431), and a Simple twin/alias per the
standing directive; otherwise the push gate fails on the new single-lane symbol.
Also run check-runtime-api-regression-push.shs (no symbol removals) - this plan removes none.

## 4. Owners
.github/CODEOWNERS maps `/src/compiler/`, `/src/compiler_rust/`, `/scripts/bootstrap/` to @ormastes;
no per-lane owner for src/runtime/ or src/lib/ (falls to default/none). Lane owners: runtime C+Rust
twin = owner TBD (doc/03_plan/runtime/ is the likely plan home); self-hosted codegen = src/compiler
(50.mir, 60.mir_opt) owner @ormastes; stdlib consumers (src/lib/common/crypto/xxh3.spl etc.) = TBD;
XXH3 lane owns the bug doc and benchmark.

## 5. Recommendation and migration (Option a, finish it)
Make the self-hosted compiler emit `rt_byte_array_new` wherever the seed already does, behind a flag.
Flag: `SIMPLE_PACKED_U8=0|1` read by the compiler at lowering time (default 1 after soak, 0 initially);
this changes emitted code only, so the runtime needs no flag and old binaries are unaffected.
PR 1 (red->green, no behavior change): characterization spec
  `test/.../packed_u8_array_repr_spec.spl`: `var b: [u8] = []; b.push(1)` then assert
  `rt_array_is_byte_packed(b)` (red on stage2, green on the seed native lane). NOTE: `rt_array_is_byte_packed` has no interpreter registration (interpreter_extern/mod.rs, 0 hits) and returns a silent nil there, so PR1 either adds that registration or the spec runs native only (no interpreter-green claim), plus a memory spec
  (16 MB push loop peak RSS < 40 MB, red today at ~135 MB).
PR 2 (GATED on PR3 audit + mixed-producer spec green; behind flag default 0): self-hosted lowering - empty `[]`/`[u8]` decl, `[0u8; n]` repeat, `.to_bytes()`-style
  producers choose `rt_byte_array_new(cap)`/`_new_len`; mirror seed lowering_expr_collection.rs:93-132.
  Fix the comprehension-over-packed-u8 MIR rejection (frontend_advisory_preprocess_port_v1.spl:94)
  in this PR, removing the @workaround. Test: PR1 spec goes green; comprehension spec green.
PR 3 (land BEFORE PR2 flips anything): dual-layout audit covering (i) runtime sites, (ii) compiler-emitted `rt_array_get` sites (expr_dispatch.spl:3607,3638; mir_lowering_stmts.spl:2242,2509,4608), (iii) `src/runtime/runtime.c:4224` `rt_bytes_to_text` (reads `rt_array_data_ptr` as uint8_t* with no flag test). For each of the 82 FLAG_BYTES sites and each non-runtime TU that reads
  `[u8]` (engine2d kernels, crypto, file io) add a mixed-layout spec (same op on packed and
  generic array gives equal results). Red where an accessor ignores the flag.
PR 4: perf - port the seed's inline typed-bytes LE load (calls.rs:3889) to the self-hosted backend
  and give `rt_typed_bytes_u64_le_unchecked` a memcpy fast path when FLAG_BYTES is set. Test:
  xxh3 64 KB bench >= 5x (bug doc baseline 332 us); correctness vs rt_xxh3_128_text golden vectors.
PR 5: flip `SIMPLE_PACKED_U8` default to 1 after one clean stage2->stage3 round-trip + test suite.
Rollback (see also section 7 caveat: deployed binaries need a stage re-bootstrap): set `SIMPLE_PACKED_U8=0` (or revert PR 5 only); arrays created before are still handled
because every runtime accessor remains dual-layout. Never remove the generic u8 path in this plan.
Native proof: the next stage2 (and stage3) rebuild via the sanctioned script
(scripts/bootstrap/bootstrap-from-scratch.sh, per .claude/rules/bootstrap.md); stdlib edits need no
build but compiler lowering changes do. Evidence = peak-RSS of the 16 MB input, xxh3 bench, plus
spec results on the stage3 binary, recorded in the bug doc.

## 6. Risks / open questions
- Whether the self-hosted lowering has another path creating `[u8]` (struct fields, fn returns,
  `Array<u8>`, generics) - literals alone will not cover them; PR 1 must enumerate creation sites.
- Generic code `[T]` with T=u8 instantiated through monomorphization may still call rt_array_new.
- Thread spawn unpacks packed arrays (collections.rs:312-370): may negate the saving in actor code
  and cost a copy; confirm for the native runtime.
- Packed arrays reaching code that assumes tagged slots (outside runtime_native.c TU, SFFI hosts,
  JIT inline paths) - the blend_mask incident (:8770) is the precedent.
- 1 GiB packed cap vs 100M generic cap: behavior change on growth/limits for large inputs.
- Interpreter (Rust twin) vs native divergence in layout is invisible to tests that only use the
  interpreter; specs must run natively.
- Which owner approves runtime changes (no CODEOWNERS entry for src/runtime): TBD.
- bug doc not in working tree on release/1.0.0; confirm it is on main before citing in PRs.

## 7. BLOCKER addendum: mixed producer/consumer (from Fable review)
- The self-hosted compiler emits a direct `rt_array_get` whenever the static element type is not U8
  (expr_dispatch.spl:3607,3638; mir_lowering_stmts.spl:2242,2509,4608). C `rt_array_get` returns the
  RAW octet for FLAG_BYTES arrays (runtime_native.c:10259-10260) while the Rust twin re-tags it
  (collections.rs:1611). Raw-octet is a PINNED C convention:
  doc/08_tracking/bug/native_index_get_packed_raw_slot_2026-10-19.md.
- Effect: once PR2 packs all `[u8]`, a packed array reaching `[T]` (generic), `Any`, or alias-typed code
  on the C lane reads wrong values (raw n instead of tagged n<<3). This is the main risk of the plan.
- Required specs (red->green, NATIVE lane, added to PR2/PR3): (1) generic `fn f<T>(xs: [T]) -> T`
  returning `xs[i]` called with a packed `[u8]`; (2) an `Any`-boxed element read of a packed array;
  (3) type-alias `[u8]` indexed through the alias. Red today only once the flag is on; write them in
  PR3 with the flag forced on in the spec build.
- Fix choice (decide in PR3, recommended = A):
  A. Flag-aware compiler sites: route the non-U8 `rt_array_get` sites through a flag-aware getter
     (`rt_bytes_u8_at`-style tagging wrapper or the existing typed accessor) so the pinned C
     convention for direct callers is untouched. Needs no new rt_* if an existing getter fits;
     otherwise a new symbol obeys section 3 (C + Rust + Simple twin).
  B. Re-tag in C `rt_array_get` (match Rust :1611). Simplest and removes C/Rust divergence, but it
     reverses the pinned convention and must update every consumer of that bug doc's contract.
- PR2 may not enable packing for all `[u8]` until the PR3 audit list is empty and the three specs are
  green on a native stage2 build.
- Rollback caveat: `SIMPLE_PACKED_U8=0` only affects binaries compiled afterward. A DEPLOYED stage
  binary that already lowers packed `[u8]` needs a stage re-bootstrap (or revert + re-bootstrap) to
  roll back; the runtime stays dual-layout so existing arrays remain valid.
