# Compiler loader packed-byte evidence gaps

Status: CLOSED WITH PLATFORM WARN

This record began as a missing-evidence inventory, not a claim that the
implementation was incorrect. PBL-01 and PBL-02 are now closed by the green
and deliberate-red receipts below. PBL-03 is closed at the admitted Rust/native
boundary; real macOS compilation remains WARN and Stage 4 remains excluded.

| ID | Code anchor | Initial required test | Current disposition |
|---|---|---|---|
| PBL-01 | `src/compiler_rust/compiler/src/interpreter_extern/sffi_array.rs:101`, `src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs:175`, and the clone/equality owners `src/compiler_rust/compiler/src/value_pointers.rs:236` and `src/compiler_rust/compiler/src/value_pointers.rs:362` | Add `packed_byte_concat_preserves_storage`, `packed_byte_clone_preserves_cow_storage`, and `packed_byte_equality_is_value_based` to `src/compiler_rust/compiler/tests/packed_byte_interpreter_semantics.rs` | CLOSED — green suite plus retained status-101 oracle receipt |
| PBL-02 | `src/compiler_rust/compiler/src/interpreter/place.rs:169` and `src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs:485` | Add `interpreter_byte_array_projected_place_mutators_write_back` to `src/compiler_rust/driver/tests/interpreter_extern.rs` | CLOSED — green focused test plus retained status-101 oracle receipt |
| PBL-03 | Historical process-lifetime leaked pointer boundary and raw dynamic fallback | Prove input-only scoped dispatch, bounds rejection, non-escape, owner ABI, and removed-symbol enforcement | CLOSED WITH WARN — focused Rust tests and retained status-101 removed-symbol receipt pass; Apple-target compilation was blocked before this crate by the Linux host C toolchain |

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

The bounded review initially found **nine production Simple files, nine
declarations, and 26 call sites** (the declaration is counted separately),
including four stored addresses. PBL-03C then removed all three HashSet uses.
The remaining live inventory is **eight files, eight declarations, 23 call
sites, and one stored address**:

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
| `src/lib/nogc_sync_mut/src/collections/hashset.spl` | 0 | 0 | MIGRATED — bounded `[u8]` indexing and retained clear |

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

### PBL-03C bounded HashSet progress

`src/lib/nogc_sync_mut/src/collections/hashset.spl` no longer declares or uses
`rt_array_data_ptr_u8`, `spl_load_u8`, `spl_store_u8`, or raw `memset` for its
occupancy bytes. Known-new insertion reads/writes `slot_used[slot]` directly;
retained clear performs a bounded O(capacity) loop. The focused spec covers
both known-new paths, clear/reuse behavior, and a source contract rejecting the
raw symbol. The admitted Stage-2 compiler native-built the focused spec with
`3 compiled, 0 failed` using:

`mkdir -p /tmp/pbl03c-stage2-cache && timeout 180 build/restart12-build11-a-r2/output/stage2/x86_64-unknown-linux-gnu/simple native-build --target x86_64-unknown-linux-gnu --backend cranelift --runtime-bundle core-c-bootstrap --source src/lib --entry-closure --threads 1 --cache-dir /tmp/pbl03c-stage2-cache --mode dynload --entry test/01_unit/lib/nogc_sync_mut/hashset_probe_spec.spl --runtime-path build/restart12-build11-a-r2/output/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority -o /tmp/pbl03c-hashset-spec-stage2`

The artifact was 6928 KB, but its unresolved `expect` stub means this is
compile evidence only. Stage 2 has no `test` command and the single direct SMF
execution attempt ended at the known exit 139, so execution remains blocked
rather than inferred.

PBL-03A's scoped interpreter prototype (7 focused Rust tests) and PBL-03B's
15 typed wrapper names were deliberately reverted: without their native/Simple
peers and codegen owner-liveness lowering, retaining either would leave an
unused interpreter-only API or uncompilable callers. Their design findings are
captured above; no partial escape route was added.

The required optimizer audit could not be executed from Stage 2. One bounded
attempt used the admitted Stage-2 compiler to native-build
`src/app/optimize/main.spl` with compiler/app/lib sources, an isolated
`/tmp/pbl03c-optimizer-cache`, and a 180-second timeout; it produced no output
or candidate and exited 124. It was not retried. Stage 2 compile evidence for
the focused HashSet spec remains valid, but optimizer findings and runtime
performance remain blocked rather than inferred.

## 2026-08-14 atomic PBL-03 closure

The eight remaining Simple owners were migrated atomically to 15 typed
array-taking family adapters plus `spl_wffi_call_i64_with_bytes`. Both native
codegens now retain the RuntimeValue owner through each provider call;
`rt_file_write_bytes` similarly lowers to `rt_file_write_bytes_array`. Native
and interpreter providers validate descriptors, own temporary material for the
call only, and never return a byte address.

All positive non-document references, registrations, headers, definitions, and
callers of `rt_array_data_ptr_u8` were removed. The only non-document occurrence
is the intentional negative HashSet source-contract assertion. The retained
status-101 receipt in
`doc/09_report/compiler_loader_packed_byte_deliberate_red_evidence_2026-08-14.md`
proves the native registry rejects restoration of the raw escape ABI; the
restored focused command passes 1/1. Scoped foreign tests pass 4/4, and
`cargo check -p simple-runtime -p simple-compiler` passed once.

Three Vulkan readback adapters remain native/JIT-only because interpreter
extern arguments are cloned Values and cannot commit destination mutation to
the caller place. They are deliberately absent from interpreter dispatch; a
focused non-vacuous registry test passes 1/1. The existing interpreter-specific
array ABI remains the interpreter path.

The Metal metallib adapter uses `DispatchData::from_bytes`, whose vendored
implementation copies the input, and enables the matching `objc2-metal`
`dispatch2` surface. An `aarch64-apple-darwin` check was attempted once but
stopped in `libmimalloc-sys` because the Linux host `cc` rejected Apple `-arch`
and deployment flags before the runtime crate compiled. Real macOS compilation
therefore remains WARN. None of this evidence is Stage 4 performance or
deployed-CLI evidence.

### Post-integration SimpleOS syscall closure

A refreshed-origin audit found one positive legacy reference outside the
original inventory: `src/os/userlib/syscall_raw.spl` still returned
`rt_array_data_ptr_u8` for filesystem and socket syscalls. That route is now
migrated to eight operation-specific adapters for open/read/write/rename and
bind/connect/send/recv. Each Simple signature passes `[u8]` owners, never an
address; rename retains both path owners, while read/recv retain the mutable
output owner through validated copyback.

`src/runtime/runtime_simpleos_syscall_adapters.c` validates paths at 1..4096,
sockaddr payloads at exactly 16 bytes, and I/O at no more than 1 MiB. It
uses production registered RuntimeValue validation, accepts packed bytes or
generic tagged integers only in 0..255, materializes call-scoped storage, and
frees all temporary storage on every exit. Readback validates the whole owner
before the syscall and commits with one non-failing representation-aware store,
so an error cannot expose a partial prefix. The shared provider is listed in
the x86_64, AArch64, and RISC-V SimpleOS sysroot builds. Its focused stubbed C
contract proves allocation/free parity, injected allocation failures, bounds,
readback, and dual-owner rename; a second production-runtime-linked test proves
packed/generic decoding, malformed/invalid rejection, and real copyback.
Compiler/common ABI guards for all eight symbols pass 1/1 each. The final
Stage-2 native-build of the Simple source contract completed with 1 compiled,
42 cached, and zero failures. An earlier intermediate artifact ended at the
known duck-typed native dispatch bug with status 132, so Stage-2 evidence is
retained as compile-only rather than execution proof.

The selected pure-Simple array owner now exports strong versions of the three
checked byte-transfer helpers; the hosted C runtime keeps weak fallbacks for
its own registered arrays. Both reject tuple and packed-u64 representations.
Stage 2 built all 18 parts of the x86_64 pure-Simple core archive, and a
host-target link that selected that archive's strong owner passed the same
packed/generic/invalid/copyback runtime test. This proves the selected-owner
link contract, not a SimpleOS target link or execution.

Exact final Stage-2 command:

`timeout 180 build/restart12-build11-a-r2/output/stage2/x86_64-unknown-linux-gnu/simple native-build --target x86_64-unknown-linux-gnu --backend cranelift --runtime-bundle core-c-bootstrap --source src --entry-closure --threads 1 --cache-dir /tmp/restart12-simpleos-syscall-stage2-cache --mode dynload --entry test/01_unit/os/apps/servers_user/arm64_payload_symbol_contract_spec.spl --runtime-path build/restart12-build11-a-r2/output/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority -o /tmp/restart12-simpleos-syscall-contract-stage2-reviewed`

After this extension the global non-document census contains only explicit
negative assertions against `rt_array_data_ptr_u8`; there is no positive
definition, declaration, or caller. These receipts prove the SimpleOS source,
ABI, and provider contract, not a target sysroot archive/link or target runtime
execution. Those target gates, the macOS Metal compile, and Stage 4 remain WARN
or excluded rather than inferred.

The broad archive emitted by the retained Stage-2 compiler still contains
undefined `rt_array_data_ptr_u8` references in discarded module sections even
though the current source census is clean. The focused selected-owner link
succeeds with section garbage collection. A fresh compiler and actual payload
archive/link remain required before promoting the target WARN.
