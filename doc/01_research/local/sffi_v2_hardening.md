<!-- codex-research -->
# Local Research: SFFI v2 Hardening

**Date:** 2026-08-21

**Baseline:** `2624da57f05e7ad1865b56493bbcb3a04e2b0dd3`
**Canonical synthesis:** `doc/01_research/platform/sffi_v2_hardening_2026-08-21.md`

This companion indexes the repository evidence behind the supplied assessment.
It does not replace or overwrite the combined research.

## Confirmed implementation seams

- `src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs`
  turns an execution with no value into `Value::Nil`.
- `src/compiler_rust/compiler/src/interpreter_call/core/macros.rs` contains the
  unit-only return guard; it is not total declared-return validation.
- `src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs` owns the
  generic integer-shaped dynamic call path.
- `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` and
  `signatures.rs` own seed extern dispatch and signature routing.
- `src/compiler/35.semantics/lint/sffi_lint.spl` and
  `src/compiler/90.tools/sffi_gen/` are existing self-hosted policy/generation
  seams, but are not one authoritative resolved ABI registry.
- `src/compiler/70.backend/sffi.spl`, native linker owners, and SimpleOS loader
  owners must agree with the interpreter rather than synthesize providers.
- `src/compiler/00.common/assurance/unsafe_capabilities.spl` contains the
  canonical `ffi` capability vocabulary; bug records show parsing/HIR carriage
  is not yet a complete lexical boundary.

## Reproduce-first evidence

| Defect | Existing evidence |
|---|---|
| Declared return mismatch/fallthrough | `test/01_unit/compiler/types/declared_return_type_enforced_spec.spl` |
| Missing extern fabricated by native link | `test/01_unit/compiler/linker/extern_unimplemented_weak_stub_fabrication_spec.spl` and its four fixture families |
| Plain `[u8]` versus `Option<[u8]>` transport | `test/01_unit/compiler/sffi_byte_array_return_not_option_spec.spl` |
| Cross-engine `[u8]` defect class | `test/01_unit/compiler/sffi_byte_array_return_class_spec.spl` |
| Unsafe capability vocabulary | `test/unit/compiler/common/assurance/unsafe_capabilities_spec.spl` |
| Resource ownership surface | `test/01_unit/compiler/resource/resource_sffi_pilot_spec.spl` |

Adjacent coverage includes backend null/layout/signature specs, hosted extern
mode agreement, SFFI lint/driver shim specs, and the C/C++/import/layout/callback
integration specs under `test/02_integration/sffi/`.

## Bug-record authority

P0 is directly supported by `declared_return_type_not_enforced_2026-08-09.md`,
`unregistered_extern_silent_nil_2026-08-01.md`,
`extern_unimplemented_links_weak_stub_fabricated_value_2026-08-18.md`,
`native_build_fabricates_weak_stub_for_unimplemented_extern_2026-08-18.md`,
`native_link_fabricates_weak_empty_extern_definitions_2026-08-01.md`, and
`sffi_u8_return_nil_and_cross_engine_len_2026-08-18.md` in
`doc/08_tracking/bug/`.

P1/P2/P4 are supported by the resource declaration, unsafe capability, and
artifact trust-anchor bug records named in the combined research. Those
records remain authoritative until implementation and verification close them.

## Local conclusion

P0 must repair each execution/link lane as one defect class. P1 must establish
one compiler-owned typed contract and generated lift path. A grep inventory,
per-lane registry, wrapper convention, or signature field alone cannot prove
the boundary.

## Post-P0 native bridge inventory

The value-returning `spl_wffi_call_i64` family is not one semantic contract.
Live callers use it for arbitrary scalars, statuses where zero is valid,
pointers where zero is invalid, booleans, lengths, and ignored destructor
returns. `spl_wffi_call_f64` serves plugins where `0.0` is valid, while the
byte-descriptor variant has one counterpart-provider caller.

No replacement sentinel is safe. The reusable repository convention is status
plus caller-owned mutable output, already used by AES `*_into` runtime bridges:
transport status zero means the bridge invoked the call and initialized the
output; the unchanged foreign result lives in the out slot. The canonical safe
owner is `src/lib/nogc_sync_mut/sffi/dynamic.spl`, exposing `Result` while the
old value-returning names remain explicit legacy-unsafe ABI during migration.

Assurance policy already defines `moderate`, `strict`, `robust`, `critical`,
and `verified`, with child serialization through `SIMPLE_SAFETY_PROFILE`.
Typed adapters run before `dynamic_sffi::try_call_dynamic`, making it the
legacy-generic choke point. Until typed policy reaches Rust in process, generic
dispatch requires a positive development opt-in; robust/critical/verified and
unknown profiles deny before library or symbol resolution with `E-SFFI-014`.

## Raw pointer-write contract audit

The interpreter and both owned C runtime providers implement
`rt_ptr_write_u8`, `rt_ptr_write_i32`, and `rt_ptr_write_i64` as void-returning
raw stores. Their canonical ABI is `(i64 address, i64 offset, exact-width
value) -> void`; in particular, the i32 value is not an i64. Invalid nonpositive
addresses or negative offsets must fail closed before dereference. The hot path
remains a validation branch followed by one direct store: it performs no heap
allocation, symbol lookup, hashing, locking, or generic marshalling.

Owned Simple declarations are not yet uniformly consistent with this ABI.
Several still claim fabricated i64/optional returns or widen the i32 argument.
Those declarations and their callers remain an explicit migration item; this
provider hardening does not establish caller-owned allocation bounds or prove
all raw-pointer users safe.

The first caller migration covers CUDA/OpenCL argument packing, Metal host
packing, GPU-lane canary writes, and WM measurement buffers. These declarations
now use the exact void result and exact i32 payload, and calls are confined to
narrow `unsafe(ffi, raw_ptr)` scopes. Removing the fabricated result also
removes optional-value construction from these per-element paths. The source
inventory improved from 33 to 40 fully tagged/contracted declarations, but 517
remain contract-documented without an unsafe tag and 13,599 remain missing
both; therefore repository-wide SFFI is still neither safe nor verified.

The follow-up exact-signature census found 41 owned declarations for the three
pointer-write symbols and 11 ABI mismatches: false i64 returns and widened i32
payloads. All 41 now match the compiler/runtime void ABI. The new
`sffi-exact-pointer-write-abi.shs` gate is called by the runtime contract audit,
so reintroducing either mismatch fails before build or execution. This is a
source/ABI guarantee only; declarations still lacking lexical unsafe metadata
and call-site bounds proofs remain in the unsafe-tag migration queue.

All 41 owned declarations in this pointer-write family now also carry explicit
`ffi` and `raw_ptr` unsafe capabilities plus an ownership/bounds obligation.
The audit rejects an exact signature whose immediately preceding declaration
metadata omits either capability. The implementation batches source parsing
rather than spawning once per file; the measured focused audit completes in
about five seconds and has zero runtime hot-path cost. Inventory state improves
from 40 to 70 `unsafe_contract_declared` rows and reduces declarations missing
both tag and contract from 13,599 to 13,569. Call-site lexical enforcement is
still incomplete in the bootstrap compiler, so the tags are honest review
metadata, not evidence that every pointer operation is memory-safe.
