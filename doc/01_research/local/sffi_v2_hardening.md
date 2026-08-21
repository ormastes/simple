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

## Raw pointer-read provider audit

The corresponding `rt_ptr_read_u8/i32/i64` interpreter and C providers had the
same fail-open descriptor and alignment hazards: extra arguments were accepted,
null or negative descriptors reached dereference, and wide reads used aligned
typed loads even though the ABI permits byte offsets. The hardened providers
require exactly two arguments, reject nonpositive addresses and negative
offsets, and use unaligned-safe i32/i64 loads. Native i32 and i64 contracts are
now compiler-registered; runtime contract coverage therefore advances to 1,093
covered and 698 missing. Constant-size C `memcpy` is used for alignment safety
and remains compiler-lowerable to a direct load; no allocation, lookup, hash,
lock, or generic marshalling is introduced on the call path. An `-O2` object
inspection confirms the i32/i64 functions compile to two descriptor tests and
one direct `mov` load, with no call to `memcpy` on the accepted path.

The exact pointer-memory audit now covers all 64 owned read/write declarations
in one batched scan (about three seconds measured). Every pointer-read
declaration has the exact two-i64 input and width-correct result contract and
explicit `unsafe(ffi, raw_ptr)` metadata. Inventory improves to 92
`unsafe_contract_declared` rows and 13,550 declarations missing both tag and
contract. As with writes, the tag records the caller-owned allocation/bounds
obligation; it does not manufacture proof while lexical enforcement remains
incomplete.

The remaining-width inventory exposed `rt_ptr_write_i16` as a live HDA audio
declaration with no owned interpreter or C provider. It is now implemented in
all three lanes as an exact `(i64, i64, i32) -> void` ABI, uses unaligned-safe
two-byte stores, rejects invalid descriptors, and is called through a narrow
`unsafe(ffi, raw_ptr)` scope after the HDA buffer-size check. The compiler-owned
runtime-symbol and ABI registries now include it. Coverage advances to 1,094
of 1,792 runtime symbols, while the missing-contract count remains 698 because
the previously absent symbol became a newly enumerated covered contract.

The performance-critical `rt_ptr_write_bytes_raw` path is now exact-arity and
return-origin aware: length zero is the only zero-result success, while a
nonempty copy with a nonpositive source/destination, negative offset, or
negative length fails closed. The Rust shim and both C providers use the same
rule. The accepted hot path remains one bulk `memcpy` plus descriptor branches;
it does not regress to per-byte boxing or copying. The exact pointer-memory
source gate now covers both owned bulk-copy declarations as well as scalar
reads/writes (67 declarations total).

## Package-signature admission audit

The package registry declared text-shaped Ed25519 externs that did not match the
canonical byte-array ABI, but its helpers never invoked them: signing returned
an empty text sentinel and silently produced HMAC instead, while verification
returned an unavailable sentinel and could accept a proxy-HMAC result. The
result was then labeled `ed25519`. This was neither Ed25519 authentication nor
a safe provider fallback.

Package signing and verification now route only through the existing checked
Ed25519 wrappers. Malformed keys, malformed signatures, provider errors, and
the current trust-store schema's missing public-key binding all fail closed.
Legacy key generation/loading reports typed SFFI/evidence errors rather than
minting mislabeled signatures. A zero-runtime-cost audit forbids direct crypto
externs, availability stubs, and HMAC-as-Ed25519 fallback in these modules.
Removing the four false declarations reduces the global missing-both inventory
to 13,545. Valid verification performs fixed-size checks followed by the same
single Ed25519 operation; no hashing, lookup, allocation, or fallback crypto
was added to the successful checked-wrapper path.

TLS server CertificateVerify also bypassed the checked wrappers: it called the
raw Ed25519 extern directly, retried when an empty signature was returned, and
used empty handshake bytes as the final error signal. The live server handshake
now calls `build_certificate_verify_checked`, which uses Result-bearing
Ed25519/ECDSA wrappers once and propagates the diagnostic into the handshake
failure. A compatibility builder remains for existing byte-structure tests but
is forbidden on the live handshake path by `crypto-sffi-checked-callers.shs`.
This removes a redundant cryptographic retry from failure cases and adds no
work to successful signing.

The compact `Result<[u8], text>` propagation form exposed a common interpreter
array-assertion bug during the TLS spec. Packed byte arrays asserted as `[u8]`
now use a tested identity cast, avoiding a copy, allocation, or traversal. The
focused Rust unit passes. The deployed `bin/simple` predates this compiler
change, so the TLS spec still observes the old behavior and reached its
three-run cap; fresh-bootstrap integration evidence remains pending. Details
are recorded in
`result_propagation_array_cast_tls_checked_signing_2026-08-21.md`.

The TLS CertificateVerify and certificate-chain RSA-PSS verification paths
also used legacy boolean wrappers that collapsed malformed bridge input and
provider failure into an invalid-signature result. They now use the existing
Result-bearing checked wrappers for SHA-256, SHA-384, and SHA-512. Each success
path still performs exactly one foreign verification operation; no retry,
hashing, lookup, or extra cryptographic operation was introduced. The static
crypto audit now forbids legacy RSA-PSS wrappers throughout `_CertVerify`.

The native PBKDF2 interpreter handlers also fabricated valid-looking inputs:
missing or wrong-typed byte arrays became empty arrays, while missing or
wrong-typed integer parameters became zero. All four SHA-family handlers now
reject malformed arguments before derivation. Valid calls retain the same
direct RustCrypto operation and output allocation. Focused tests cover
SHA-256/384/512 vectors plus malformed argument rejection; their test decoder
now accepts the canonical packed byte-array representation.

The shared Cranelift/bootstrap text converter returned `RuntimeValue::NIL` for
every wrong-typed argument. That allowed malformed module names, object paths,
shell commands, hash paths, and file contents to reach foreign providers as a
null runtime string; their missing-argument branches separately fabricated
zero, false, `-1`, or empty text. The common converter and these text-bearing
handlers now return typed runtime errors. Valid calls still perform one type
match and the same direct runtime call, with no lookup, copy, retry, or added
allocation. Five focused Cranelift SFFI tests pass, including malformed text
arguments and null-positive-length foreign result validation.

The adjacent Cranelift module-management boundary had the same issue for
integer handles and raw pointer/length descriptors. Module construction,
finalization, release, object emission, function declaration, and string-data
declaration now reject missing/wrong-typed integers, negative lengths, and
null pointers paired with positive lengths before entering unsafe runtime code.
The checked helpers are inline and the valid path remains direct; validation
adds only type/descriptor branches, not allocation, lookup, or copying. The
focused raw-object descriptor regression passes.

The next Cranelift declaration/context group is now covered by the same
fail-closed decoder: global data, data/function address import, function
imports and parameter attachment, AOT definition, signature creation/update,
function begin/end/definition, and block creation no longer turn absent or
wrong-typed handles into zero/nil/false. Name spans reject negative lengths and
null-with-positive-length descriptors before unsafe entry. One focused
sabotage test exercises the group. Inline checks preserve the direct valid
call shape and introduce no heap work or registry lookup.

Cranelift block switching/sealing, block parameters, scalar constants, null
constants, and the macro-generated binary arithmetic family now use checked
integer/float/boolean extraction as well. Missing or mismatched operands can
no longer become zero, `0.0`, or false before unsafe code generation. The
helpers are inline, numeric widening remains explicit for valid float inputs,
and every valid wrapper still makes exactly one backend call. A focused test
covers block, constant, boolean, float, and generated binary rejection.

All 15 remaining legacy sign/verify declarations in the canonical signature
module are now explicitly `unsafe(ffi)` and document their sentinel contract:
verification collapses malformed bridge input into `0`, while signing may
produce an empty signature. The crypto audit rejects any future raw
sign/verify declaration without adjacent FFI-unsafe metadata. These legacy
ABIs are not thereby verified or safe; the tags prevent them from masquerading
as ordinary safe interfaces while callers migrate to checked `Result` APIs.
Inventory improves to 108 `unsafe_contract_declared` rows and 13,529 missing
both tag and contract. An annotation-only change has no call-path cost.
