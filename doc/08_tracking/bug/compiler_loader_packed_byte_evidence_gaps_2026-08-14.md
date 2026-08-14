# Compiler loader packed-byte evidence gaps

Status: OPEN

This record began as a missing-evidence inventory, not a claim that the
implementation was incorrect. PBL-01 and PBL-02 are now closed by the green
and deliberate-red receipts below; PBL-03 remains open.

| ID | Code anchor | Initial required test | Current disposition |
|---|---|---|---|
| PBL-01 | `src/compiler_rust/compiler/src/interpreter_extern/sffi_array.rs:101`, `src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs:175`, and the clone/equality owners `src/compiler_rust/compiler/src/value_pointers.rs:236` and `src/compiler_rust/compiler/src/value_pointers.rs:362` | Add `packed_byte_concat_preserves_storage`, `packed_byte_clone_preserves_cow_storage`, and `packed_byte_equality_is_value_based` to `src/compiler_rust/compiler/tests/packed_byte_interpreter_semantics.rs` | CLOSED — green suite plus retained status-101 oracle receipt |
| PBL-02 | `src/compiler_rust/compiler/src/interpreter/place.rs:169` and `src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs:485` | Add `interpreter_byte_array_projected_place_mutators_write_back` to `src/compiler_rust/driver/tests/interpreter_extern.rs` | CLOSED — green focused test plus retained status-101 oracle receipt |
| PBL-03 | The process-lifetime leaked byte boundary at `src/compiler_rust/compiler/src/interpreter_extern/sffi_array.rs:708` and the raw dynamic fallback at `src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs:654` | Create `src/compiler_rust/compiler/tests/packed_byte_foreign_capability_lifetime.rs` with `packed_byte_foreign_capability_is_input_only`, `packed_byte_foreign_descriptor_rejects_out_of_bounds`, and `packed_byte_foreign_capability_cannot_escape_call` | `cd src/compiler_rust && cargo test -p simple-compiler --test packed_byte_foreign_capability_lifetime` passes after a retained deliberate-red receipt |

Owner: compiler interpreter/SFFI owner. Final reviewer: highest-capability
reviewer. The Rust seed may exercise these Rust tests but may not substitute for
the separate self-hosted Stage 4 admission and performance gates.

## 2026-08-14 post-sync regression repair

After rebasing onto `7ac900316dd5`, the existing focused semantic test exposed
that the general place route had started intercepting a bare mutable
`ByteArray`. Its empty projection could not be rebuilt by `updated_root`, so
`bytes.push(7u8)` returned the enlarged value while leaving the identifier at
length four. Bare mutable packed bytes now fall through to the identifier/COW
owner; projected places and bare frozen receivers retain the general place
route.

The driver tests named “interpreter” were also using `run_code`, which compiles
and executes SMF through `Runner` and therefore did not exercise the Rust
interpreter owner they claim to cover. Their packed-byte cases now use a focused
direct-interpreter helper that clears module/interpreter state for each source.
Fresh evidence: `packed_byte_interpreter_semantics` passed 1/1 and the four
`interpreter_byte_array_identifier_mutators` cases passed 4/4. PBL-01 remains
open for concat/clone/equality and PBL-02 remains open for projected-place
coverage; this repair does not promote either row.

## 2026-08-14 PBL-01/PBL-02 closure

The remaining Rust-interpreter boundary cases are now implemented. Packed plus
packed `rt_array_concat` returns `Value::ByteArray`; the semantic suite covers
concat, COW clone, and value equality and passes 4/4. The representation-level
concat unit passes 1/1. The direct-interpreter projected-place mutation case
passes 1/1, in addition to the previously retained 4/4 identifier cases.
The implementations and final Rust-interpreter behavior are green. The required
semantic deliberate-red receipts are retained in
`doc/09_report/compiler_loader_packed_byte_deliberate_red_evidence_2026-08-14.md`:
PBL-01 rejected `Ok(4105)` with status 101 and PBL-02 rejected exit code 1718
with status 101. Both named oracle mutations were restored exactly without
rerunning the already-authoritative green criteria. PBL-01 and PBL-02 are
therefore proved at the Rust interpreter boundary.
These results are not Stage 4 or deployed-CLI evidence.

## 2026-08-14 PBL-03 ABI blocker review

There is no genuine scoped integration that preserves the current interpreter
ABI. `rt_array_data_ptr_u8` returns a pointer encoded as an `i64`; the producer
call ends before a later foreign call consumes that integer, so neither the
adapter nor Rust's lifetime system can bound its use. A callback wrapper is not
enough: once it exposes `as_ptr()`, safe code can return the raw pointer or its
integer address even when the wrapper descriptor itself is lifetime-bound.

The production interpreter registration still leaks the materialized byte
buffer for process lifetime, and dynamic SFFI string marshalling retains the
same leak pattern. PBL-03 therefore needs an explicit ABI migration: either
pass packed bytes directly into a typed one-call foreign adapter, or mint an
opaque descriptor token that the sole foreign-dispatch owner resolves and
revokes during that call. Both require migrating callers; treating a token as
the existing raw pointer would break native consumers. The three named tests
must target that production route, include compile-fail or equivalent escape
enforcement, and retain a deliberate-red receipt before PBL-03 can move to
PROVED.

### Complete caller inventory and migration decision

The bounded review found **nine production Simple files, nine declarations,
and 26 call sites** (the declaration is counted separately). Four call sites
store the returned address in a local before a later call. The inventory is:

| Owner | Uses | Stored address | Migration family |
|---|---:|---:|---|
| `src/lib/gc_async_mut/cuda.spl` | 3 | 0 | typed CUDA byte-input wrappers |
| `src/lib/gc_async_mut/gpu_lane/cuda_lane_session.spl` | 2 | 0 | typed CUDA upload wrappers |
| `src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl` | 10 | 0 | typed Vulkan byte-input wrappers |
| `src/lib/nogc_sync_mut/io/font_sffi.spl` | 1 | 0 | typed font byte-input wrapper |
| `src/lib/nogc_sync_mut/io/metal_sffi.spl` | 1 | 0 | typed Metal byte-input wrapper |
| `src/lib/nogc_sync_mut/io/vulkan_sffi.spl` | 1 | 0 | typed Vulkan byte-input wrapper |
| `src/lib/nogc_sync_mut/sffi/spl_fonts.spl` | 4 | 0 | typed font/shaping byte-input wrappers |
| `src/lib/nogc_sync_mut/spec/evidence/counterpart/dynlib_provider.spl` | 1 | 1 | generic dynamic-library one-call byte argument |
| `src/lib/nogc_sync_mut/src/collections/hashset.spl` | 3 | 3 | bounded array operations; no FFI pointer |

Runtime and compiler owners that must migrate with those callers are
`src/compiler_rust/runtime/src/value/collections.rs`,
`src/compiler_rust/compiler/src/interpreter_extern/sffi_array.rs`,
`src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs`,
`src/compiler_rust/compiler/src/interpreter_extern/mod.rs`, both codegen
registries, the common runtime-symbol allowlists, `src/runtime/runtime.h`,
`src/runtime/runtime_native.c`, and `src/runtime/simple_core/core_array.spl`.
The freestanding RISC-V definition and C self-check callers are compatibility
surfaces and must be removed or migrated in the same final ABI cutover.

No production-safe implementation was made in this bounded lane. A token
returned from `rt_array_data_ptr_u8` cannot be introduced compatibly: every
compiled consumer currently interprets the `i64` as an address. A callback
surface is also not an enforceable Simple contract because captured closures
cannot cross SFFI and safe wrapper code can still convert a borrow to an
integer. The staged `resource` syntax is not yet source-reachable. Keeping the
old raw symbol beside a new API would also leave the escape route open and
make `packed_byte_foreign_capability_cannot_escape_call` vacuous.

### Required production shape

1. Add consuming operations whose Simple signatures accept `[u8]`, offset,
   and length, never an address. Fixed foreign families get typed wrappers;
   `DynLib` gets one `call_*_with_bytes` operation whose Rust owner performs
   marshalling, dispatch, and cleanup in one stack frame.
2. In the interpreter owner, validate the descriptor before materialization,
   own a `Box<[u8]>` for exactly the dynamic call, and drop it on every return
   and unwind path. Nested calls own independent buffers; no TLS scratch and
   no process-lifetime leak are permitted.
3. In native codegen/runtime, keep the packed array owner live across the
   consuming call and project its backing address only inside that call.
   Non-packed input must fail closed or use a call-scoped owned copy.
4. Replace HashSet's three pointer uses with bounded byte load/store/clear
   operations. They are not foreign calls and must not inherit an SFFI escape
   mechanism merely for speed.
5. After every caller is migrated, remove `rt_array_data_ptr_u8` from extern
   registration, runtime symbol allowlists, public headers, Simple core, and
   all runtime implementations. The link/check failure for any new declaration
   of that removed symbol is the enforceable equivalent of compile-fail escape
   prevention.

The foreign callee itself is trusted not to retain the transient C pointer;
Simple can prevent the capability/address from escaping its call boundary but
cannot make a malicious C library forget an address it copied. Documentation
and tests must state that trust boundary rather than claim memory safety inside
arbitrary foreign code.

### Parallel implementation split

- **PBL-03A — generic interpreter dispatch:** implement the one-call `DynLib`
  byte argument, nested-call ownership, checked offset/length, and guaranteed
  cleanup. Own `dynamic_sffi.rs` and its focused Rust tests.
- **PBL-03B — typed GPU/font consumers:** add array-taking runtime wrappers and
  migrate CUDA, Vulkan, Metal, and font owners. Preserve exact native ABI
  semantics and retain family-specific smoke coverage.
- **PBL-03C — collection/raw-symbol removal:** replace HashSet pointer access,
  migrate compatibility/self-check callers, then delete all registrations and
  definitions of `rt_array_data_ptr_u8`.
- **Merge owner — lifetime acceptance:** land
  `packed_byte_foreign_capability_lifetime.rs`, retain deliberate-red receipts
  for input-only, bounds rejection, nested independence, cleanup on failure,
  and old-symbol escape rejection, then run the single focused gate once.

These lanes must merge atomically or behind a temporary internal-only build
flag. Landing a public token, a second raw-pointer spelling, or an unused typed
adapter is explicitly not progress on PBL-03.
