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

The remaining Cranelift comparison, memory, stack, control-flow, direct and
indirect call, conversion, function lookup, and raw function-pointer handlers
now use the checked decoders too. Null JIT function pointers, malformed raw
argument vectors, missing operands, and wrong scalar types fail before unsafe
invocation. The permissive numeric converters and all scalar/unit fabricated
fallbacks have been removed from this module. A focused sabotage test passes,
and `cranelift-sffi-fail-closed.shs` permanently gates these source invariants
without adding runtime work.

The interpreter rustls client boundary previously converted missing or
wrong-typed hosts, SNI names, payloads, ports, connection handles, sizes, and
timeouts into nil runtime strings or integer zero. All nine handlers now reject
those arguments before calling the provider. Runtime input strings and copied
text outputs are scoped and released, removing the prior per-call allocation
leak; valid network operations remain single provider calls. Four focused tests
pass, including malformed arguments, null-positive-length output, valid empty
text, and scoped string ownership. A source-only TLS audit prevents permissive
fallbacks or unowned runtime strings from returning.

The native tiered-JIT bridge likewise converted malformed handles and names to
zero/empty text and converted execution failure into `-1`, which collides with
a legitimate compiled function result. Argument decoding and handle lookup now
fail closed, while missing compiled functions remain an intentional boolean
absence result. Execution failures are typed runtime errors, so all `i64`
results remain representable. The valid hot path still performs the same map
lookup and one execution call, without added allocation. A focused sabotage
test passes. All raw JIT declarations in the compiler and four library manager
modules are explicitly `unsafe(ffi)`, enforced by a source-only audit.

The interpreter SHA-1/base64 boundary accepted missing, wrong-typed, and legacy
raw-pointer inputs as empty bytes; invalid hasher handles returned nil. Checked
text/byte/integer decoding now rejects those states, while explicit empty input
remains valid. Stateful finish operations distinguish invalid handles and
consume their state. The WebSocket accept path no longer attempts a redundant
free after consuming finish, and all raw SHA-1 declarations are explicitly
`unsafe(ffi)`. Focused malformed-input and empty-input tests pass. The valid
path retains one hash/encoding operation; the removed double cleanup reduces
work. A source-only audit gates the decoder, unsafe tags, and ownership rule.

The interpreter `rt_io_file_*` family used shared decoders that fabricated
`-1`, caller-selected defaults, false, zero bytes, or an empty byte array for
missing and wrong-typed arguments. File descriptors, modes, sizes, offsets,
whence values, permissions, and write buffers now fail before OS I/O when their
contract is malformed; explicit empty byte buffers remain valid. Operational
filesystem failures retain the declared legacy status results. The valid path
keeps one existing byte extraction and one OS operation. A focused sabotage
test passes, all raw file declarations are tagged `unsafe(ffi)`, and a
source-only audit enforces both properties.

The low-level asynchronous I/O driver bridge indexed arguments directly and
coerced wrong types to zero, empty text, or an empty C string. It now uses an
explicit Rust `unsafe extern` block, checked scalar/text/C-string decoding,
and bounded text spans for send/write operations. Embedded NUL paths,
negative/overlong lengths, malformed handles, null-positive-length poll data,
and null backend names fail before lifting or invocation. The dispatch helper
is inline; valid payloads remain borrowed and each operation performs one FFI
call without copying. A focused pre-FFI sabotage test and source-only audit
pass.

The cached `spl_winit` buffer router replaced embedded-NUL text, BMP paths,
and configured provider paths with empty C strings or silently skipped them.
All caller-controlled C strings now reject embedded NUL, and the `dlopen`
declarations use an explicit Rust unsafe extern block. The successful buffer
path retains cached symbol resolution and one native call; no pixel copy or
lookup was added. The GUI-feature focused test and source-only audit pass.
At this stage the router was still an unverified dynamic provider. The
subsequent sealed-admission work below authenticates its artifact, while its
raw Rust calls correctly remain explicitly unsafe because signing does not
prove provider semantics.

The router also ignored `rt_winit_buffer_free`'s result and always reported
success, while invalid or failed pixel readback became an empty array. The
consumer now preserves the provider's free result and verifies both phases of
the pixel-count/fill protocol. The Rust provider reports false for missing
buffers and rejects undersized output capacity rather than returning a
success-sized count without writing. A display-independent provider contract
test passes. These checks are constant-time metadata comparisons around the
existing allocation/copy and add no extra native call.

The `spl_winit` loader now supports one-time cryptographic artifact admission.
When `SIMPLE_SPL_WINIT_REQUIRE_SIGNATURE=1`, or any seal evidence is present,
it reads the exact provider bytes before `dlopen`, checks the adjacent
`<artifact>.sha256`, and verifies `<artifact>.sig` as an Ed25519 signature over
`"SIMPLE-SPL-WINIT-ARTIFACT-V1\\0" || SHA256(artifact)` using the trusted
32-byte hex key in `SIMPLE_SPL_WINIT_ED25519_PUBKEY`. Partial, malformed,
mismatched, and tampered evidence fails closed. A generated-key test proves
valid admission and both artifact/signature sabotage rejection. Verification
is confined to the cached load path, so there is no per-call hash, signature,
file I/O, or lookup. Development loading without evidence remains permitted
but explicitly unsafe. On Linux, the loader now opens the artifact once,
hashes bytes from that open file, and calls `dlopen` through
`/proc/self/fd/<fd>` while retaining the file handle. This closes the
path-replacement check/use race without changing the cached per-call path.
Other Unix targets still load by pathname and therefore remain ineligible for
critical-safe classification. Even on Linux, signature admission authenticates
bytes but does not prove the provider's full semantic, ownership, ABI-registry,
or provenance obligations.

All 15 remaining legacy sign/verify declarations in the canonical signature
module are now explicitly `unsafe(ffi)` and document their sentinel contract:
verification collapses malformed bridge input into `0`, while signing may
produce an empty signature. The crypto audit rejects any future raw
sign/verify declaration without adjacent FFI-unsafe metadata. These legacy
ABIs are not thereby verified or safe; the tags prevent them from masquerading
as ordinary safe interfaces while callers migrate to checked `Result` APIs.
The Cocoa compositor boundary had 12 untagged raw declarations and 20 calls
outside lexical unsafe scopes. Its Rust real provider also reported success
when image creation failed and for an unimplemented blur, while C and Rust
size/coordinate arithmetic could overflow before allocation or clipping. All
declarations now document ownership/sentinel semantics, every call has one
minimal `unsafe(ffi)` scope, and both providers fail closed on unsupported or
invalid storage. The C provider additionally rejects embedded-NUL titles and
failed bitmap/image construction. Rust provider tests, C warnings-as-errors
syntax, Simple syntax, and a dedicated source audit pass. These changes add no
native call, lookup, hash, or allocation to the hot path; checked arithmetic
replaces potentially undefined or panicking arithmetic. The macOS real C lane
still needs race-focused execution and signed-artifact evidence, so this is
contract-hardened rather than fully verified.

The rebuilt inventory now records 124 `unsafe_contract_declared` rows and
13,456 missing both tag and contract. Twelve Cocoa declarations are in the
declared state. Metadata and lexical unsafe scopes compile away and have no
call-path cost.

The editor SDL bridge exposed raw `SDL_Window*` values as public `i64`
handles. A stale or forged value could therefore reach SDL without validation.
The bounded 64-slot generation table now belongs to canonical `rt_sdl2_*`
rather than only the editor aliases, so every C SDL2 window consumer receives
the same validation. Creation performs the only linear free-slot scan;
width/height, destruction, properties, and presentation decode a slot in O(1).
The provider rejects stale generations, off-owner-thread calls, invalid pixel
length/capacity/data relations, invalid dimensions, and table exhaustion.
App `window_sffi` is now a facade over the library-owned declaration/call
boundary, removing 53 duplicate raw declarations and their drift risk. The
hosted compositor removed four unused declarations; its five remaining externs
carry ownership/sentinel contracts and its six calls have minimal lexical
`unsafe(ffi)` scopes. The 16 editor declarations and 19 calls remain similarly
contracted/scoped.

A compiled C sabotage self-test covers valid, wrong-thread, forged, stale,
removed, and full-table handles. Simple syntax, presentation failure
integration, and the source audit pass. The hot path performs one acquire
load, constant integer arithmetic, and one bounded array lookup, with no
mutex, map, scan, allocation, hashing, double wrapping, or extra native call.
The canonical library owner still has 66 generic unsafe declarations whose
exact per-function sentinel/borrow contracts and lexical wrapper scopes must
be migrated, and the dynamically loaded SDL artifact lacks signed admission;
SDL2 therefore remains contract-hardened but not fully verified.

The refreshed inventory records 145 `unsafe_contract_declared` rows and
13,378 rows missing both tag and contract. Removing duplicate declarations is
an assurance improvement rather than merely changing ledger classifications.

SDL2 display discovery previously converted provider/load failures into valid
looking values: zero displays, the name `"Unknown"`, zero bounds, and `96.0`
DPI. The C boundary now returns disjoint failure sentinels (`-1`, null,
`INT64_MIN`, or `-1.0`) and rejects invalid indices/off-owner-thread calls.
The Simple boundary declares all 11 exact sentinel contracts, confines calls
to two lexical `unsafe(ffi)` regions, and exposes `Option` for count, primary
display, complete lists, and individual records. A partial record fails as a
whole instead of mixing fabricated and real fields. The compiled C sabotage
self-test covers unavailable display sentinels, and Simple syntax plus a
source audit pass. Existing enumeration still performs the same SDL field
queries; safety adds only the already-required owner-token load and scalar
comparisons, with no hashing, allocation, lookup table, or extra native query.
The inventory now records 156 `unsafe_contract_declared` rows and 13,367 rows
missing both tag and contract. SDL artifact admission remains unsigned.

SDL2 clipboard reads previously collapsed provider failure into valid empty
text, allocated an untracked `strdup` copy on every successful read, and
represented both “no text” and provider failure as `false`. The canonical C
provider now returns null on read failure, uses one capacity-tracked cache
released at shutdown, and exposes a `-1/0/1` query contract. Simple lifts these
states to `text?`, `bool?`, and public `Result` values, while the Rust dispatcher
preserves nullable absence and rejects invalid UTF-8 rather than inserting
replacement characters. The two old Result-free host-bridge adapters remain
explicitly unsafe because their fixed function-pointer ABI still collapses
errors; replacing that bridge is follow-up work.

The native sabotage fixture, warnings-as-errors optimized C build, Rust family
tests, Simple syntax checks, and a dedicated source audit pass. The successful
read path makes the same single SDL query and byte copy as before, while cache
reuse removes repeated allocation churn; no hash, symbol lookup, mutex, or
additional native call was added. The refreshed inventory records 159
`unsafe_contract_declared` rows and 317 `unsafe_contract_missing` rows. These
contracts are locally checked but the dynamically loaded SDL artifact is still
unsigned and lacks sanitizer/proof receipts, so the SDL2 family is not fully
verified.

The canonical SDL2 cached-event detail boundary had 14 declarations carrying
only a generic unsafe label, and nine otherwise validating Simple wrappers
were themselves broadly unsafe. Each declaration now records its exact zero
sentinel/precondition or borrowed-text lifetime, while the validating wrappers
confine authority to nine lexical `unsafe(ffi)` call scopes. The legacy raw
poll and winit-compatibility adapters remain unsafe because their zero sentinel
still conflates provider absence with “no event”; the metadata documents that
limitation rather than claiming a safe result.

This slice deliberately preserves the hot path: event details still read the
single cached `SDL_Event` in O(1), event text remains a borrowed zero-allocation
view, and no native call, validity probe, lock, allocation, hash, or lookup was
added. Simple syntax and the dedicated event contract/performance-shape audit
pass. The refreshed inventory records 173 `unsafe_contract_declared` rows and
303 `unsafe_contract_missing` rows. Provider signing and the ambiguous poll
sentinel remain open, so SDL event handling is contracted but not verified.

SDL2 poll and wait previously used `0` both when no event was available and
when the dynamic provider could not be loaded. The C ABI now reserves `-1` for
provider admission failure without changing successful event codes. The
canonical `EventBatch` carries an explicit `is_valid` bit, maps failure away
from a usable event handle, and performs the raw call in a lexical unsafe
scope. The compositor and Web UI direct consumers disable their provider after
the first negative status, preventing both fabricated “no event” and a tight
failure-retry loop.

The event hot path still makes exactly one `SDL_PollEvent` or `SDL_WaitEvent`
call and adds only scalar comparisons already required to classify the event;
there is no allocation, lock, error-string query, hash, or lookup. The
optimized C build, three Simple syntax checks, and poll/event source audits
pass. Inventory classification remains 173 contracted and 303 uncontracted
unsafe declarations because poll/wait were already documented in the previous
slice. SDL internal wait errors are still indistinguishable from timeouts, and
the raw compatibility adapter still exposes integer status, so this boundary
is fail-closed for provider absence but not fully verified.

SDL2 polled keyboard and mouse state previously returned `0` for unavailable
providers, invalid key/button identifiers, and valid false/coordinate-zero
results. The C provider now uses `-1` for boolean/status failure and
`INT64_MIN` for unavailable coordinates. Three safe Simple wrappers lift those
sentinels to `bool?` and `Position?`, confine raw calls to lexical
`unsafe(ffi)` scopes, and are exported through both sync and async facades.
Raw integer entry points remain exported only as explicitly unsafe ABI access.

The change adds no native query: key/button wrappers make one existing SDL
call, while position still requires the existing x and y calls. There is no
allocation, lock, hash, map, error lookup, or retry. The optimized warnings-as-
errors C build, Simple checks for both facades, and a dedicated sentinel and
performance-shape audit pass. Inventory now records 177 contracted and 299
uncontracted unsafe declarations. SDL artifact signing and runtime sanitizer
receipts remain absent, so these functions are fail-closed but not verified.

SDL2 millisecond and nanosecond clocks previously returned valid timestamp
zero when provider loading or performance-frequency discovery failed. Both raw
ABIs now reserve negative status for failure; the nanosecond conversion also
saturates at `INT64_MAX` before signed overflow. Safe `i64?` wrappers confine
the FFI calls and are exported through both runtime facades. The Web UI frame
pacer now stops and reports failure when the clock disappears instead of using
fabricated time or entering an unbounded busy wait.

Successful millisecond queries still make one `SDL_GetTicks` call and
nanosecond queries one `SDL_GetPerformanceCounter` call after the existing
frequency cache is warm. Safety adds scalar comparisons only, with no lock,
allocation, hash, lookup, or error-string query. Optimized C compilation, three
Simple checks, and the clock performance-shape audit pass. Inventory improves
to 179 contracted and 297 uncontracted unsafe declarations. The provider
artifact and clock semantics still lack signed/sanitizer evidence, so they are
fail-closed rather than verified.

Six canonical SDL2 window mutations (title, resizable, size, position, show,
and hide) previously returned `void`; their Simple wrappers therefore reported
success after stale handles, invalid dimensions, or rejected coordinates. The
C ABI and Rust dispatcher now carry boolean status for arities one through
three. Five public wrappers validate that status in lexical `unsafe(ffi)`
scopes, and compositor resize commits its dimensions/pixel buffer only after
the native resize succeeds. The stale-handle sabotage fixture covers all six.

Each mutation still performs one generation-table lookup and at most the same
single SDL mutation call. No validation query, allocation, lock, hash, map, or
retry was added. Optimized C compilation, Rust SDL family tests, three Simple
implementation checks, the six-example compositor spec, and the ABI/performance
audit pass. Inventory improves to 185 contracted and 291 uncontracted unsafe
declarations. SDL functions whose underlying API itself returns `void` prove
only accepted arguments/live handles, not post-call OS success, and provider
artifact evidence remains unsigned; this is fail-closed contract hardening,
not full verification.

SDL2 window width/height and x/y position reads previously returned `0` for a
stale, forged, or off-owner-thread handle, fabricating valid geometry. Width
and height now use `-1`; coordinates use `INT64_MIN`. The four raw declarations
record those exact contracts, and `window_get_size`, `window_get_position`,
inner size, and outer size expose typed absence with lexical unsafe call scopes.
The generation sabotage fixture asserts all four invalid-handle results.

The wrappers retain the existing two native reads per size or position request;
no extra validity query, allocation, lock, hash, lookup, or retry was added.
Optimized C compilation, both Simple facade checks, and the read-contract hot-
path audit pass. Inventory improves to 189 contracted and 287 uncontracted
unsafe declarations. Successful OS reads still rely on SDL semantics and the
provider remains unsigned, so this is fail-closed but not fully verified.

SDL2 lifecycle declarations for init, quit, window creation/destruction, and
presentation previously had generic contracts; quit and destroy returned void,
and five public wrappers carried whole-function unsafe authority. Quit and
destroy now return boolean status across C, Rust dispatch, and Simple. The
canonical wrappers use lexical scopes and propagate status; Web UI uses those
ownership/presentation wrappers and logs destruction failure. Init/create keep
their established zero failure sentinel with exact contracts. Invalid-owner
quit and stale-handle destroy are covered by the generation sabotage fixture.

Lifecycle changes are cold. The frame hot path remains exactly one
`rt_sdl2_present_rgba` call with its existing O(1) handle validation and pixel
conversion; no extra call, allocation, lock, hash, lookup, or retry was added.
Optimized C compilation, Rust family tests, three Simple checks, and lifecycle
ABI/performance auditing pass. Inventory improves to 194 contracted and 282
uncontracted unsafe declarations. SDL’s void shutdown/destroy primitives and
the unsigned loaded artifact still prevent a fully verified classification.

SDL2 cursor visibility, grab, and warp previously returned void, so stale
handles, wrong-owner calls, out-of-range coordinates, and `SDL_ShowCursor`
failure were reported as success. All three now return boolean status across
C, Rust dispatch, and Simple. Their public wrappers propagate status from
minimal lexical `unsafe(ffi)` scopes. The native sabotage fixture verifies
wrong-owner/stale-handle refusal for all three operations.

Cursor changes are not frame rendering operations. Each path retains one
existing handle validation and at most its original single SDL mutation call;
visibility uses the existing `SDL_ShowCursor` return rather than an additional
query. No allocation, lock, hash, map, or retry was added. Optimized C, Rust
family, Simple, and cursor ABI/performance audits pass. Inventory improves to
197 contracted and 279 uncontracted unsafe declarations. SDL’s void grab/warp
primitives prove accepted inputs rather than post-call OS state, and signed
provider evidence remains absent, so the family is not fully verified.

SDL2 window flags previously returned zero for a stale, forged, or wrong-owner
handle, fabricating `false` for visibility, maximized, and fullscreen state.
The native function now reserves `-1` for invalid handles and the three public
wrappers expose typed absence. Quit-state reads and clearing now validate the
SDL owner thread; clearing returns explicit status instead of silently
mutating or doing nothing.

Each property wrapper still performs exactly one generation-table lookup and
one `SDL_GetWindowFlags` query. The quit-state operations add only the existing
owner-thread comparison and remain cold control paths. No allocation, retained
memory, lock, hash, dynamic lookup, error query, or retry was added. Optimized
C, Rust bridge tests, four Simple checks, and the ABI/performance audit pass.
Inventory improves to 200 contracted and 276 uncontracted unsafe declarations.
The dynamically loaded SDL artifact is still unsigned and lacks bound
sanitizer/proof receipts, so these contracts are fail-closed but not verified.

Nine SDL2 property mutations previously used integer success values across the
C ABI, Rust dispatcher, and Simple declarations; eight public wrappers also
held whole-function unsafe authority. They now use boolean status end-to-end,
have exact stale-handle, invalid-bound, SDL-failure, or unavailable-capability
contracts, and confine raw calls to lexical `unsafe(ffi)` scopes. The invalid
generation sabotage fixture now covers every operation in the family.

Each wrapper preserves its prior one-call branch shape (minimize/maximize select
one of two possible calls). There is no new native query, allocation, retained
memory, lock, hash, dynamic lookup, error query, or retry. Optimized C, eight
Rust bridge tests, four Simple checks, and the mutation ABI/performance audit
pass. Inventory improves to 208 contracted and 268 uncontracted unsafe
declarations. SDL's void property APIs can prove accepted inputs/live handles,
not post-call compositor state; signed artifact admission and bound sanitizer
or proof receipts are still absent, so this family is not fully verified.

SDL2 display discovery had disjoint native failure sentinels but all eleven raw
declarations still advertised only a generic ABI, the display-name declaration
incorrectly claimed a non-null `text`, and monitor construction admitted numeric
sentinels as ordinary geometry. The declarations now state exact nullability and
sentinels. Monitor count returns `i64?`; monitor information returns `Monitor?`
only after validating name, bounds, and DPI inside a lexical FFI scope.

Count retains one native query and monitor information retains its existing six
queries. No query, allocation, retained memory, lock, hash, lookup, error query,
or retry was added. Optimized C, eight Rust bridge tests, four Simple checks,
and the display contract/call-shape audit pass. The final generic error-text
declaration now states nonnull borrowed ownership, and the unused unchecked
void fullscreen ABI was removed from C, Rust dispatch, and Simple. Inventory
improves to 220 contracted and 255 uncontracted unsafe declarations; the
canonical SDL module itself is 65/65 contracted. The provider artifact and
runtime evidence remain unsigned/unbound, so this is safe lifting of known
sentinels rather than full verification.

The owned-production inventory is substantially broader than the canonical SDL
slice. After excluding tests, examples, and vendored runtime/compiler sources,
the current declaration-row census contains 223 fully tagged/contracted rows,
255 tagged rows missing contracts, 347 contracted rows missing unsafe tags, and
7,584 rows missing both. These are declaration rows rather than unique symbols;
the complete inventory contains 3,967 distinct extern symbols across all
classifications. Therefore no repository-wide safe/verified claim is justified.

The first Winit read slice exposed a cross-engine ABI split: Simple requested an
interpreter-only tuple size and floating scale symbol, while the Rust provider
exports scalar width/height and milli-scale C ABI functions. The wrapper now
uses those native symbols in both engines. Width, height, scale, and x/y
position reserve disjoint failure sentinels and lift invalid reads to typed
absence. Five of Winit's thirty raw declarations are now contracted/tagged.

Size and position retain two scalar reads; scale retains one. The changes add
no allocation, retained memory, lock, hash, dynamic lookup, error query, or
retry. The Simple check, Rust provider tests, GUI-feature interpreter sentinel
test, and Winit call/memory-shape audit pass. Winit provider signing and bound
runtime evidence remain absent, so the family is hardened but not verified.

Winit lifecycle release functions previously reported success for every event,
window, and loop handle, including stale handles, while the canonical Simple
declarations discarded their results. Rust provider and GUI interpreter lanes
now return failure when the owned object is absent. The canonical wrappers
propagate loop/window release status, and event drains retain lexical unsafe
scopes around the mandatory release call. Creation declarations now state their
nonpositive failure sentinels. Winit reaches 10/30 contracted declarations.

Release still performs the same single map removal/state transition; no extra
provider call, allocation, retained memory, lock acquisition, hash pass,
dynamic lookup, error query, or retry was added. Rust provider tests, the
GUI-feature interpreter stale-handle test, Simple check, and lifecycle
call/memory-shape audit pass. The owned-production census becomes 228 fully
contracted rows and 7,579 rows missing both tag and contract (the other gap
classes remain 255 and 347). Signed Winit admission/evidence remains absent.

Winit staging previously accepted negative dimensions by coercing them to one,
multiplied dimensions without checked byte capacity, exposed its borrowed raw
pointer without a declared lifetime, and ignored the caller's dimensions during
present. The Rust provider and GUI interpreter now reject nonpositive/out-of-
range/overflowing extents and require present dimensions to match the exact
staging descriptor. The Simple wrapper checks signed multiplication before
length comparison and gives pointer copy/present calls exact unsafe contracts.

The frame path retains one existing `[i64]` to `[u32]` conversion buffer, one
bulk pointer copy, and one present call. It adds only integer validation; there
is no extra allocation, retained memory, copy, provider call, lookup, lock,
hash, error query, or retry. Five Rust provider tests, the GUI interpreter
descriptor test, Simple check, and staging memory/call-shape audit pass. Winit
is 13/30 contracted; owned production becomes 231 contracted and 7,576 rows
missing both. Artifact signing and bound sanitizer/proof evidence remain open.
Winit fullscreen declarations previously disagreed across lanes: Simple used a
boolean ABI while the native provider exports integer status, and invalid state
reads became `false`. Both engines and the wrapper now use integer status with
negative typed absence for invalid fullscreen reads. Position mutation has an
exact status contract and native coordinates are range-checked instead of
truncated to `i32`. All three public wrappers use lexical FFI scopes.

Each operation retains one provider call and adds no allocation, retained
memory, copy, lookup, lock, hash, error query, or retry. Five provider tests,
the GUI interpreter sentinel test, Simple check, and window-state call/memory-
shape audit pass. Winit is 16/30 contracted; owned production becomes 234
contracted and 7,573 rows missing both. During inventory verification, detached
read-only census processes from earlier yielded sessions were explicitly
terminated to avoid wasting host CPU/memory; no repository data was affected.

Winit event admission previously declared a native wait symbol that the Rust
provider did not export, and both poll/wait collapsed invalid or disconnected
loops into ordinary `0` no-event/timeout. The provider now exports wait using
one bounded native event pump; both lanes reserve `-1` for admission failure.
Safe close polling returns `bool?`, and `WinitInput.is_valid` distinguishes
provider loss while every positive event remains released exactly once.

Poll and wait retain one pump and one queue pop per admission attempt. No busy
loop, sleep, allocation, retained event, additional provider call, lookup,
lock, hash, or retry was added. Five provider tests, GUI interpreter invalid-
loop test, three Simple checks, the five-example wrapper spec, and event
admission call/memory audit pass. Winit is 18/30 contracted; owned production
becomes 236 contracted and 7,571 rows missing both. The remaining twelve event
accessors still require lifetime/type contracts and signed artifact evidence.

The twelve Winit event accessors now reserve disjoint failure values: `-1`
for kinds, keys, booleans, lengths, bytes, and buttons, and `INT64_MIN` for
coordinates and wheel deltas where zero is valid. Native and interpreter lanes
agree, safe wrappers validate before lifting, and borrowed text is copied before
the event's single release. The final three Winit fullscreen/position operations
also carry explicit live-handle/status contracts, completing the canonical
module's 30/30 declaration contract inventory.

The event hot path retains the prior provider-call count, performs no lookup,
hash, retry, sleep, or additional allocation, and reads every accessed field at
most once. Provider/interpreter sentinel tests, Simple check and lint, the
five-example integration spec, and a call/memory-shape audit pass. This closes
the Winit declaration-contract slice only; signed provider admission and
artifact-bound proof/sanitizer receipts remain required before Winit or global
SFFI can be called verified.

Duplicate Winit staging bindings in `hosted_backend_winit.spl` and the BMP
export in `dual_backend.spl` were untagged and exposed two provider defects.
Native and interpreter staging-clear paths clamped invalid dimensions and used
unchecked extent multiplication; the native BMP writer accepted dimensions
that did not match the borrowed pixel length before constructing its slice.
Both lanes now reject zero, negative, overflowing, over-`isize`, and mismatched
extents before allocation or pointer/slice construction. The four duplicate
declarations carry exact minimal unsafe contracts and calls use lexical scopes.

Presentation retains one staging acquisition, one write per pixel, and one
present call, with no added buffer, lookup, lock, hash, retry, or sleep. The BMP
comparison lane retains one write call per output and now reports failure.
Native provider tests, the GUI interpreter test, two Simple checks, lint, and a
source call/memory-shape audit pass. The broader WM seam spec remains red only
for its documented pre-existing missing FreeBSD implementation; it passed the
other ten examples. Signed artifact admission remains outstanding.

The duplicate `hosted_input_backend.spl` lane declares tuple-return keyboard
and mouse accessors that exist only in the synthetic interpreter dispatcher;
the native Winit provider exports scalar accessors instead. Replacing each
tuple with multiple scalar calls would add provider dispatches and interpreter
locks on a hot input path. This lane therefore requires a generated typed
snapshot/status-out thunk shared by native and interpreter, not a compatibility
rewrite that trades ABI correctness for a performance regression.

The Chromium shell's seven scalar Winit duplicates can be hardened without
that tradeoff. They now carry ownership/sentinel contracts and minimal lexical
FFI scopes; negative admission, stale event-kind, release failure, and teardown
failure propagate through the existing boolean run result. Each admitted event
is still decoded once and released once before the next poll. No call,
allocation, lookup, lock, hash, or retry was added. Simple check/lint, the
19-example Chromium interaction spec, and the call/memory-shape audit pass.

Lifecycle return correction: event, window, and event-loop release have exactly
two outcomes, so their canonical ABI is now `bool`, not an integer status. The
Rust provider exports C-compatible booleans, the interpreter returns
`Value::Bool`, and canonical/Chromium/game2d declarations agree. Safe consumers
check `false` and propagate or fail closed; this fixes the provider contract
rather than wrapping the integer mismatch.

Game2D's interpreter-only keyboard tuple was replaced by
`rt_winit_event_key_packed`, a versioned one-call scalar snapshot implemented in
both Rust provider and interpreter. Bit zero carries pressed state and upper
bits carry the non-negative keycode; `-1` is the failure sentinel. This retains
one dispatch and one interpreter lock per keyboard event while making native
and interpreter ABI identical. Admission, kind, packed decode, release, and
teardown failures now close the backend rather than fabricating input.

The new `scripts/audit/rt-safety-census.shs` performs a fail-closed owned-source
`rt_*` census and accepts signed/verified state only from an explicitly trusted,
artifact-bound admission ledger. On 2026-08-22 it reports:

| Metric | Count |
| --- | ---: |
| Simple `rt_*` declaration rows | 12,610 |
| Distinct declared symbols | 3,172 |
| Rows explicitly tagged unsafe | 455 |
| Rows with a documented/typed contract | 540 |
| Verified evidence rows | 0 |
| Signature-verified rows | 0 |
| Verified and signed rows | 0 |
| Fail-closed unsafe rows | 12,610 |
| Untouched rows (no unsafe tag, contract, or evidence) | 11,879 |
| Symbols with source-signature variants | 297 |

Implementation-shaped owned definitions are: C 2,301 rows / 1,821 distinct
symbols / 82 files; Rust 2,161 / 2,097 / 172; Simple 584 / 535 / 51; C++ 211 /
211 / 1. Symbols may intentionally appear in multiple language lanes, so those
language distinct counts are not additive. Static annotations remain claims:
without a trusted admission receipt bound to the exact artifact, the tool keeps
the row unsafe.

The census now also emits a provider-family migration queue and has a checked-in
one-way ratchet. The largest untouched families are `rt_file` (2,791 rows),
`rt_process` (1,045), `rt_env` (469), `rt_time` (368), and `rt_cuda` (353).
The ratchet rejects increases in untouched or signature-variant counts and
decreases in unsafe tags, documented contracts, or trusted admissions. It runs
only during audit/build verification and adds no runtime lookup, hash, branch,
allocation, or retained memory.

Verification note: the non-incremental GUI compiler run selected six tests by
the broad `stale_` filter. Both intended Winit sentinel/lifecycle tests passed;
an unrelated existing JIT struct-field test failed because `rt_struct_alloc`
was unresolved and the module correctly refused a potential null jump. This is
not counted as a Winit pass or silently discarded; the focused Winit evidence
is the two named passing tests plus the provider and static contract audits.
