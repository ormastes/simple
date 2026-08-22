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
| Simple `rt_*` declaration rows | 12,650 |
| Distinct declared symbols | 3,177 |
| Rows explicitly tagged unsafe | 474 |
| Rows with a documented/typed contract | 560 |
| Verified evidence rows | 0 |
| Signature-verified rows | 0 |
| Verified and signed rows | 0 |
| Fail-closed unsafe rows | 12,650 |
| Untouched rows (no unsafe tag, contract, or evidence) | 11,899 |
| Symbols with source-signature variants | 297 |

Implementation-shaped owned definitions are: C 2,312 rows / 1,830 distinct
symbols / 87 files; Rust 2,161 / 2,097 / 172; Simple 592 / 543 / 52; C++ 211 /
211 / 1. Symbols may intentionally appear in multiple language lanes, so those
language distinct counts are not additive. Static annotations remain claims:
without a trusted admission receipt bound to the exact artifact, the tool keeps
the row unsafe.

The census now also emits a provider-family migration queue and has a checked-in
one-way ratchet. The largest untouched families are `rt_file` (2,795 rows),
`rt_process` (1,035), `rt_env` (469), `rt_time` (367), and `rt_cuda` (353).
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

Rust-seed lexical enforcement no longer drops raw extern authorization at MIR.
A HIR-only checker now traverses nested statements and expressions while
preserving `UnsafeBlock` scope, and the central HIR-to-MIR entry rejects an
unscoped module-local extern call as `E-SFFI-002` in critical/verified profiles.
The profile decision is process-cached and emitted target code is unchanged;
there is no application hot-path or memory cost. Focused tests pass 2/2. This
does not yet close raw-pointer or inline-assembly enforcement, nor does it turn
any unsigned provider into verified evidence.

The first `rt_time` provider slice removes fabricated-zero failure behavior for
the canonical wall-clock, monotonic-nanosecond, and monotonic-microsecond ABI.
Linux/Unix and Windows C lanes now return the disjoint negative sentinel on
clock failure or representational overflow; derived micro/millisecond functions
propagate it instead of integer division laundering `-1` into `0`. All native
timespec values are initialized before use. The Rust boundary provides inline
checked `Option<i64>` lifts, while the canonical Simple wrappers carry exact
unsafe/sentinel contracts, one minimal lexical FFI scope, and an explicit panic
on violation.

Successful Simple wrappers still make exactly one provider call and add only
one predictable negative comparison; no allocation, symbol lookup, hash,
per-call mutex, retry, or retained object was added. `runtime_time.c` removes its unsynchronized Unix
baseline state, and Windows initialization uses the platform one-time primitive.
Failure sabotage passes for all four derived C entry points, the live epoch suite
passes 6/6, Rust sentinel lifting passes, C syntax checks and Rust clippy pass,
and the census advances by three tags/contracts/untouched rows. This is verified
behavioral evidence, not signed artifact admission: globally signed rows remain
zero.

The follow-on progress/timestamp slice changes initialization and reset from
void to a real C/Rust/Simple boolean ABI. C progress state is thread-local, so
parallel test workers cannot race over a process-global start value, and every
clock call is checked. Failed initialization/reset returns `false`; failed
seconds/elapsed reads return `-1.0`; a first successful elapsed read may still
legitimately return zero. Negative clock regression is a contract failure, not
an empty duration. The safe Simple progress facade uses three minimal lexical
FFI scopes and panics on violations; the interpreter now lifts lifecycle status
as `Value::Bool` rather than `Nil`.

The elapsed hot path remains one clock read and arithmetic, with thread-local
static storage, no heap allocation, map, hash, retry, or per-call mutex. C
failure sabotage, Rust lift tests, interpreter ABI tests, and Simple checks pass.
Seven additional declaration rows are tagged and contracted. During integration,
concurrent `main` added 41 declarations and 33 untouched rows; the ratchet caught
the stale baseline. A detached census of the exact parent established 12,651 /
11,916, and this slice advanced that authoritative parent to 11,909. After the
final rebase, an upstream declaration removal leaves 12,650 total and 11,908
untouched. These figures preserve both upstream movement and this slice's
improvement. Signed/verified admission remains zero.

The first `rt_process` slice contracts the nine canonical process operations in
`src/app/io/process_ops.spl` and confines their raw calls to nine minimal lexical
FFI wrappers. Rust runtime and interpreter child publication now returns a
positive PID only after the existing registry lock owns the `Child`; a poisoned
registry kills and reaps the child before returning `-1`. Malformed argument
arrays fail before spawn instead of silently dropping non-text elements.

Successful publication still performs one lock and one map insertion, with no
new allocation, lookup, retry, sleep, or retained state. Runtime sabotage and
malformed-input tests pass, the interpreter crate passes `cargo check`, Simple
check/lint and Rust Clippy pass with pre-existing warnings, and the optimizer
reports no new wrapper allocation/dispatch concern. Nine rows become explicitly
unsafe and contracted, reducing untouched rows to 11,899. Artifact-bound signed
admission remains zero, so all 12,650 rows remain classified unsafe.

The second `rt_process` slice contracts all twelve process declarations in the
canonical `std.nogc_sync_mut.io.process_ops` owner and confines each raw call to
one minimal lexical `unsafe(ffi)` wrapper. The live timeout relay now reads only
the appended stdout/stderr ranges through the checked file facade. This removes
the prior whole-file-per-poll quadratic I/O and allocation pattern while keeping
the same observation cadence, child registry, and final captured output.

The focused multi-burst regression passes. Module check and the process contract
audit pass; lint still reports the module's pre-existing public primitive API
errors, so lint is not globally green. The optimizer finds no new allocation,
lookup, or dispatch concern. The current census contains 12,659 declarations:
C++ 211 definitions/211 symbols/1 file; C 2,301/1,821/82; Rust 2,161/2,097/172;
Simple 584/535/51. Of these, 486 are unsafe-tagged, 572 have contracts, 11,896
remain untouched, and all 12,659 remain fail-closed unsafe because signed and
verified artifact admissions remain zero.

The system-boundary ownership slice removes the duplicate implementation in
`std.nogc_sync_mut.ffi.system`: it is now an explicit compile-time facade over
the canonical `std.nogc_sync_mut.sffi.system` owner. All 45 public functions,
including the previously omitted all-limits process API in the async facade,
remain exported. The canonical owner's seven process hooks and native-execution
hook now have explicit sentinel contracts and uniquely named, allocation-free
lexical FFI scopes. This removes 40 duplicate declaration rows without adding a
runtime wrapper, lookup, allocation, or dispatch; optimizer findings for the
legacy facade fall from 20 to zero.

Owner/facade checks, lint, the existing 12-case return-contract regression, and
the static one-call/no-allocation audit pass. The census now contains 12,619
declarations: C++ 211 definitions/211 symbols/1 file; C 2,313/1,831/87; Rust
2,161/2,097/172; Simple 592/543/52. There are 494 unsafe-tagged rows, 575
contracted rows, and 11,849 untouched rows. Signed and verified admissions are
still zero, so all 12,619 declarations remain fail-closed unsafe.

The next process sweep deletes the unimported seed-era
`sys/sffi/process.spl`. Its eight declarations included three dead hooks, two
genuinely missing hooks, and duplicates of live process owners; retaining or
tagging them would preserve a false API surface. A static owner gate prevents
that declaration file from returning.

The widely used `io_runtime` process path exposed a separate performance
constraint. Delegating its five duplicates through imported aliases makes the
current JIT treat the aliases as unresolved externals and deoptimize the whole
module to the interpreter, with its own 100–1000x warning. That consolidation
was rejected and recorded as a compiler bug. The direct path remains JIT-capable
and unchanged in allocation/dispatch shape; its five declarations now carry
explicit sentinel contracts and one-call lexical FFI scopes. Module check, the
three-case tuple/exit-code regression, optimizer analysis, and static process
audit pass. Lint still reports the module's existing primitive-public-API debt.

The census is now 12,611 declarations and 3,174 symbols: 499 unsafe-tagged, 580
contracted, 11,836 untouched, and 296 signature-variant symbols. The
`rt_process` family has 1,032 rows with 999 untouched. Language implementation
statistics remain C++ 211/211/1, C 2,313/1,831/87, Rust 2,161/2,097/172, and
Simple 592/543/52. There are still zero trusted signed/verified admissions, so
all 12,611 declarations remain fail-closed unsafe.

The signed-admission slice removes the caller-authored
`RT_VERIFIED_ADMISSION_TRUSTED=1` assertion. Admission now recomputes the exact
provider, canonical-source snapshot, build-input, compiler, ABI-registry, and
verification-report SHA-256 identities; validates a canonical passing report;
and verifies a raw Ed25519 signature with a provider-scoped key from a separate
canonical trust store. Each admitted row is bound to both the runtime symbol
and its exact source-signature hash, so one ABI variant cannot promote another.
Canonical-order, stale-report, artifact-tamper, substituted-signature,
untrusted-key, and duplicate-trust sabotage tests pass. All work occurs once in
the audit/admission lane; no runtime call path gained hashing, lookup, locking,
allocation, or signature verification.

The upstream slim parse-shard change exposed four new untouched declarations.
The unnecessary raw exit was removed in favor of returning the existing error
code. The remaining file probe, path expansion, and nullable environment lookup
retain their slim dependency closure but now carry explicit sentinel contracts
and minimal lexical `unsafe(ffi)` wrappers. Importing the broad semantic
facades here would regress the parse-shard memory fix by pulling the compiler
back half into the child. The resulting census is 12,614 declarations: 502
unsafe-tagged, 583 contracted, and 11,836 untouched. Production signed evidence
is still zero, so no declaration is yet claimed safe or verified.

The census now separates the complete declaration population into mutually
exclusive ownership scopes without excluding any row. Of 12,614 declarations,
6,296 are production declarations (480 tagged, 399 contracted, 5,718 untouched),
688 are bootstrap-library declarations (20 tagged, 17 contracted, 655
untouched), and 5,630 are test declarations (2 tagged, 167 contracted, 5,463
untouched). Every scope has zero signed admissions and remains fail-closed
unsafe. The contract gate proves that scope totals equal the complete census
and rejects unknown paths, preventing a production row from disappearing into
an exclusion. This is audit-only and adds no runtime work.

The raw-runtime lint now recognizes two narrow forms of explicit containment:
an `@unsafe(... capabilities: [ffi])` immediately attached to a raw declaration,
and a raw call indented inside `unsafe(capabilities: [ffi])`. Declaration
authority does not leak into later ordinary code, so an uncontained call after
a tagged declaration still emits `RAW-RT-002`. Ordinary files retain the
single-`contains("rt_")` fast path. The performance fixture completes its clean
~889 KB input in 14–38 ms and 2,000 raw findings in 2.54–2.76 s under the
existing interpreted ceilings. The two newly contained parse-shard modules lint
without RAW-RT findings. Four pre-existing auto-fix expectations remain failing
and are recorded separately; they do not affect the new containment cases.

The first canonical production file-read slice found a provider inconsistency:
native C and Rust runtime implementations return nil for an unreadable file,
while the Rust interpreter fabricated empty text. The interpreter source now
returns `Value::Nil`, with a focused Rust unit proving that valid empty text and
failure remain distinct. The canonical facade exposes `Result<text, text>` and
keeps the legacy empty fallback only in the compatibility API. The success hot
path is unchanged; failure now uses the nil singleton rather than allocating an
empty string, and the checked facade adds only the required null branch. The
deployed bootstrap remains stale, so cross-lane verification is pending rebuild.

An unused-boundary sweep then removed 66 production/bootstrap declarations of
`rt_file_read_text` whose only occurrence was the declaration itself. No call,
wrapper, or runtime path changed. This reduces the complete census from 12,614
to 12,548 rows and untouched rows from 11,835 to 11,770; production is now
6,231 rows with 5,653 untouched, bootstrap-library is 687 with 654 untouched,
and tests remain 5,630 with 5,463 untouched. Verified-and-signed admissions
remain zero, so all 12,548 rows remain fail-closed unsafe. Six affected compiler
modules pass focused checks. A combined 60-file check was stopped after several
minutes under the runaway guard; the static proof confirms every removed symbol
had no call occurrence. Removing dead declarations adds no hot-path work and
slightly reduces parsing and name-resolution input.

A second exact-occurrence sweep covered every other `rt_file_*` symbol and
removed 33 more declaration-only boundaries across 23 files. It also removed
one now-unused unsafe attribute and the documentation owned solely by a dead
declaration. The census is now 12,517 declarations, 11,741 untouched, 502
unsafe-tagged, 582 contract-documented, and zero verified-and-signed. Production
is 6,207 rows with 5,631 untouched; bootstrap-library is 678 with 645 untouched;
tests are 5,632 with 5,465 untouched. All 12,517 remain fail-closed unsafe. The
11 changed compiler files pass together, every removed symbol has zero remaining
occurrence in its file, and census/ratchet gates pass. A bounded 12-file mixed
check was stopped after five minutes at about 336 MB RSS under the convergence
guard; it produced no source diagnostic. This slice deletes compile-time input
only and adds no runtime branch, allocation, lookup, or hashing.

Five live/comment-shadowed `rt_file_read_text` declarations were then removed
from modules that already imported the canonical `read_file_text` facade. Four
direct calls now use that facade; one declaration had only a comment mentioning
the symbol, exposing a false negative in the earlier text-occurrence sweep. The
five modules pass together. The compatibility result remains text with an empty
fallback, but nullable foreign handling is now owned by one checked boundary.
The added branch occurs only after file I/O; there is no per-call registry,
signature, hash, allocation, or generic dispatch. The census is now 12,512
declarations, 11,736 untouched, and zero verified-and-signed; production is
6,202 declarations with 5,626 untouched.

The canonical file-existence predicate now owns an explicit lexical `ffi`
unsafe boundary and documents its boolean sentinel contract: `false` covers a
missing or inaccessible path and provider failure, while `true` asserts the
provider observed an existing path. Six application-local raw declarations and
their pass-through wrappers were replaced by the canonical facade. The seven
affected modules pass together. Application call depth is unchanged (one local
wrapper became one canonical wrapper), and canonical internal calls use lexical
unsafe blocks directly, so no helper call, allocation, lookup, hashing, or
signature verification was added. The census is now 12,506 declarations,
11,729 untouched, 503 unsafe-tagged, 583 contract-documented, and zero signed
admissions; production is 6,196 declarations with 5,619 untouched.

Plugin command, plugin registry, and wrapper-generator text reads now import
`read_file_text` under their existing `file_read` name. This compile-time alias
replaces each local one-line raw wrapper, so call depth remains one while the
nullable contract is centralized. All three modules pass together. The census
is now 12,503 declarations, 11,726 untouched, and zero signed admissions;
production is 6,193 declarations with 5,616 untouched.

Canonical file-write and recursive-directory-create declarations now carry
explicit false-sentinel contracts and every canonical call is lexically
contained by `unsafe(ffi)`. Plugin registry and wrapper generator removed four
raw declarations/pass-throughs in favor of direct facade imports. The audit
chain migrated from the publicly exported raw write symbol, allowing that raw
export to be deleted. Four affected modules pass together. The successful write
path remains one typed foreign call and its existing status branch; directory
creation/retry remains failure-only. The census is now 12,499 declarations,
11,720 untouched, 505 unsafe-tagged, 585 contract-documented, and zero signed
admissions; production is 6,189 declarations with 5,610 untouched.

The remaining ten test imports of the raw text-read export now use the canonical
`read_file_text` name directly, allowing both raw read and raw write exports to
be removed. Attempting a compact import alias exposed a resolver defect: the
consumer alias captured the dependency module's internal name and recursively
called `file_read` until stack overflow. The defect is recorded; raw access was
not restored. The RV64 runtime-link contract passes 2/2 through the canonical
export. The installer-font spec now reads correctly but exposes two unrelated
stale assertions, also recorded. This export cleanup adds no runtime layer or
per-call security work; consumers call the same canonical function directly.

The general `app.io` facade no longer exports the shell-backed function named
`rt_file_rename`. All six consumers now use canonical `file_rename`, whose real
raw declaration is tagged, false-sentinel contracted, and lexically contained.
The obsolete shell wrapper was deleted. This is performance-positive: rename no
longer spawns `/bin/sh` and `mv`, and instead makes one typed runtime call with
one status branch. Seven changed source modules pass together. The integration
spec executes 19 examples with 15 passing and four unrelated maintenance
failures; it is not claimed fully green. Census/ratchet pass at 12,499
declarations, 11,719 untouched, 506 tagged, 586 contracted, and zero signed
admissions. The compatibility `file_ops` surface retains a semantic
`file_rename` wrapper, but it delegates to the typed provider rather than
spawning a shell.

The general time facade no longer exports raw-looking `rt_timestamp_now` or
`rt_sleep_ms` names. Their semantic replacements are `timestamp_now` and
`sleep_ms`. More importantly, `sleep_ms` no longer launches `/bin/sh` once or
twice per delay; it calls the typed runtime thread-sleep provider exactly once
for positive delays. That raw provider is tagged and lexically contained. Eight
changed source modules pass, and the retry/backoff suite passes all 31 examples.
The census/ratchet passes at 12,499 declarations, 11,718 untouched, 507 tagged,
586 contracted, and zero signed admissions. This removes two semantic functions
with raw names and one shell/process dependency from the delay path.

The database extended-test runtime helpers no longer fabricate timestamp `0`,
PID `12345`, or hostname `localhost`. Semantic `timestamp_now`, `process_id`,
and `host_name` helpers call canonical providers, and all persisted run/tracking
evidence uses those values. Five affected database modules pass. Together with
the time-facade rename, the implementation census drops to 587 Simple `rt_*`
definitions, 542 distinct symbols, in 49 files. Declaration safety remains
12,499 total, 11,718 untouched, 507 tagged, 586 contracted, and zero signed.

Live playback pitch no longer resolves to the constant-zero implementation in
`audio_effects.spl`. `runtime_audio.c` now applies pitch through the existing
generation-checked playback slot and miniaudio's direct `ma_sound_set_pitch`
operation. The raw integer status declaration is tagged and called only inside
one lexical `unsafe(ffi)` block; ordinary audio callers import the boolean
`audio_set_pitch` lift, so invalid handles and non-finite or non-positive pitch
fail as `false` rather than looking applied. The hot path adds no allocation,
registry lookup, hashing, signing, or process call: it uses the audio mutex,
one slot check, one direct provider call, and one status comparison. The six
unimplemented node-graph effect declarations, constant-zero implementations,
raw exports, and self-confirming tests were deleted because no production
caller or foreign provider exists. C warning-as-error syntax checking, focused
Simple lint, five Rust dispatcher tests, and the Simple contract (2/2) pass.
The census and ratchet pass at 12,493 declarations, 11,711 untouched, 508
tagged, 586 contracted, and zero verified/signed admissions. Implementations
are C++ 211, C 2,323, Rust 2,161, and Simple 580 rows.

The soft JIT facade no longer claims ignored backend or optimization requests
succeeded. It identifies its actual provider as `interpreter`, accepts only
automatic/interpreter selection, rejects Cranelift and LLVM requests, reports
native JIT unavailable, and accepts only optimization level zero. Integer
execution now carries an internal `(success, value, error)` result, so a real
`-1` return is preserved while compilation/non-integer failures cannot become
successful values. The fabricated empty last-error and zero clear-error APIs
and their public exports were removed. This improves the call path: the safe
integer API consumes the result directly instead of executing a separate
post-call last-error operation. Both duplicate compatibility modules pass
source checks and lint, and the capability/numeric guard passes 3/3. Census and
ratchet pass at 12,492 declarations, 11,711 untouched, 508 tagged, 585
contracted, and zero verified/signed; Simple `rt_*` implementations drop to
576 rows (533 distinct symbols) across 48 files.

JIT string execution no longer maps missing source and execution failure to the
same empty text as a legitimate successful `""` result. The raw-looking
`rt_exec_manager_execute_string` Simple implementation was removed; its single
owner now returns `Result<text, text>`, with `Ok(out)` preserving empty output
and explicit `Err` values for missing source and failed execution. There are no
external production callers requiring a compatibility fallback. The path still
performs one source read and one interpreter run, with no additional lookup,
allocation, process, hash, or error-state pass. Both compatibility modules
check, focused lint passes, and the numeric/capability/string guard passes 4/4.
Census and ratchet remain at 12,492 declarations, 11,711 untouched, 508 tagged,
585 contracted, and zero verified/signed; Simple implementations are now 574
rows and 532 distinct symbols across 48 files.

The SDL2 window owner no longer contains/export two dead `rt_winit_*`
compatibility aliases: present duplicated the canonical checked presentation
path and redraw returned unconditional `true` without recording a request.
Production callers already use semantic `window_present_rgba` and
`window_request_redraw`; the real Rust winit provider retains its independent
generation/owner validation and command send. Two unused scale-factor APIs that
fabricated `1.0` were also removed, while borrowed SDL event destruction now
has an explicit unit/no-release contract instead of boolean success. No runtime
branch, call, allocation, or state was added. Four facade/owner modules check,
focused lint passes, SDL event/display audits pass, and rendering guards pass.
Census/ratchet remain at 12,492 declaration rows with zero signed admissions;
untouched rows fall to 11,710, contracted rows are 586, and Simple `rt_*`
implementations fall to 572 rows (530 symbols) across 48 files.

The general I/O debug façade also exposed eight dead or misleading compatibility
functions: debug run returned unconditional zero, condition polling fabricated
empty text, condition reporting discarded its input, four fault setters returned
`true` despite the canonical ABI being unit-valued, and duplicate Vulkan/UPX
capability probes bypassed their canonical owners. No repository consumer used
these aliases. They are removed from the owner and both export layers rather
than tagged unsafe or replaced with new state. This deletes a shell-spawning UPX
probe and adds no branch, allocation, lookup, or synchronization. Four affected
modules check, focused lint passes, debugger state passes 42/42, and the fault
numeric guard passes 2/2. Census/ratchet remain at 12,492 declaration rows,
11,710 untouched, 508 tagged, 586 contracted, and zero signed admissions; Simple
implementations fall to 564 rows (522 symbols) across 48 files.

Signal handling had an unconditional `rt_signal_handler_available() == true`
precheck even though the only authoritative capability result is the existing
`rt_signal_install` status. The fabricated predicate is removed; installation
now performs one direct raw call and returns its checked status, saving the
precheck branch. Four raw signal/atexit declarations are explicitly
`unsafe(ffi)`, and semantic wrappers contain the only minimal lexical unsafe
regions. Atexit registration no longer stores a callback when provider
installation fails. Two unused app-local duplicate signal modules are deleted.
Checks and lint pass; the current checked-in bootstrap seed cannot execute the
fixture because it fail-closes with `unknown extern function:
rt_signal_install`, so behavioral provider verification is not claimed. The
broad tooling spec also remains independently red due existing seed semantic
resolution failures and an 8.9-second formatter threshold breach. Census and
ratchet pass at 12,487 declarations, 11,701 untouched, 512 tagged, 586
contracted, 558 Simple implementation rows (519 symbols) across 46 files, and
zero signed admissions.

Signal callback storage is now structurally bounded to 33 entries: one slot for
each signal accepted by the hosted provider (`0..31`) plus one atexit slot.
Repeated signal and atexit registrations replace their existing slot, and a
new distinct entry fails closed at capacity. Dispatch remains a single linear
pass over only registered callbacks and registration remains bounded O(33),
with no per-dispatch allocation, lookup table, lock, process, or hashing work.
The `COLL008` static lint previously warned on every global push even when its
own recommended capacity guard was present. It now proves a dominating
`global.len() >= capacity` return guard before the push; tests retain warnings
for unbounded growth and post-push guards. Focused compiler/signal checks and
lint pass, as do the collection lint tests. Full compiler, lib, MCP, and LSP-MCP
source checks pass. Broader release evidence remains red independently: the
MCP stdio integration did not complete under the bootstrap seed, core compile
smoke produced SMF rather than the expected executable result, and the native
MCP smoke lacks `bin/simple_mcp_server`. None is promoted to verified evidence.

The `std.nogc_sync_mut.ffi.io` and `.sffi.io` modules were duplicate foreign
declaration owners (232 and 262 lines) with already-divergent text-read and
file-lock contracts. `ffi.io` is now a 22-line explicit compile-time façade
over the more complete `sffi.io` owner. Remaining crypto-system fixtures import
the semantic byte read/write APIs rather than raw `rt_file_*` names. This adds
no runtime wrapper, branch, allocation, lookup, or synchronization; it removes
one declaration/validation surface and 211 net lines. The façade checks and
lints, both helper modules check, and the two canonical crypto/signature system
specs pass through the interpreter. Census/ratchet pass at 12,453 declarations,
11,670 untouched, 510 tagged, 585 contracted, and zero signed admissions.
The lower tag count is intentional deletion of duplicate unsafe declarations,
not loss of protection; canonical owner tags remain.

Cross-engine file metadata/hash semantics are now aligned. The native C and
Rust runtime providers already return `-1` for missing file size and `nil` for
a failed SHA-256 read, but the interpreter fabricated `0` and empty text. The
interpreter now returns the same `-1`/`nil` contract, preserving the real
zero-byte size and the valid 64-character SHA-256 digest of an empty file as
successful values. This changes only failure construction: no extra syscall,
read, hash pass, allocation, lookup, or hot-path branch is introduced. Six
focused Rust file-provider tests pass, including exact missing-size and
empty-file-versus-failure hash cases. Higher-level optional/result lifting and
signed artifact admission remain open, so this is cross-lane provider
correction rather than full verification.

The canonical line-array and mmap-byte facades now preserve the provider's
nullable failure state as `Result.Err`; legitimate empty files remain
`Ok([])`. Both paths perform one provider read and do not add an existence
probe, last-error query, registry lookup, allocation, or hash pass. The two
focused interpreter specs pass 3/3 and 12/12. The refreshed census contains
12,454 declarations, 513 unsafe-tagged rows, 587 contracted rows, 11,669
untouched rows, and zero verified/signed admissions.

The census tool itself had a scalability defect: recursive `grep -Ff` with
thousands of symbol needles remained live for more than an hour. It now scans
each Simple source once and filters call names through an in-memory symbol
hash. A complete backing census finishes in 34.09 seconds with 75,124 KiB peak
RSS; the enclosing safety census finishes in 75.03 seconds with 75,560 KiB
peak RSS. This is audit-time work only and adds no runtime/SFFI call overhead.

Both HIR safety analyzers previously recognized only externs declared in the
same module, so import/re-export could erase raw-call identity. They now treat
every `rt_*` and `spl_*` callee as intrinsically FFI-unsafe, independent of the
module-local extern table. The prefix check is compile-time, constant in the
short prefix length, and precedes the old linear table scan; generated/runtime
code receives no new branch, lookup, allocation, or wrapper. Rust tests pass
4/4 and the self-hosted safety spec passes 7/7. The broad source check printed
four successful 32-file passes but failed to terminate and was stopped, so it
is not promoted to completed verification.

The canonical Torch raw owner now tags all 135 declarations as FFI-unsafe;
compatibility families re-export this owner rather than duplicating authority.
The two raw aliases carry function-level unsafe authority and retain their
single direct call, so no handle initialization, sentinel workaround, lookup,
allocation, or extra branch was added. Focused check and lint pass. The global
census is 12,454 declarations, 645 tagged, 587 contracted, 11,537 untouched,
and zero verified/signed admissions. The unchanged contract count is
intentional: an unsafe tag is not a null/status/ownership contract.

Backing classification previously ignored `.cc`/`.cpp`/`.cxx`, falsely calling
live Torch functions missing. It now finds 105 Torch declarations backed by
owned C++ source, 24 interpreter-backed, and 6 deployed-binary-backed. A new
C++ boundary census reports 211 definitions, 209 without `noexcept` or a local
catch barrier, 31 pointer-boundary rows, and zero verified/signed. Its ratchet
passes. Source backing remains unsafe evidence only: `torch_sffi.cpp` requires
versioned status/out adapters and a universal exception barrier before safe or
critical admission.

CUDA had three declaration owners for the same low-level ABI. The no-GC sync
and GC async `ffi` modules are now explicit compile-time facades over the one
no-GC sync `sffi` owner (through the existing no-GC async facade). This removes
54 declaration rows without runtime forwarding. All 34 canonical declarations
are explicitly FFI-unsafe; the generic tag deliberately makes no contract or
verification claim. Four modules check and the owner lint is clean. The census
is now 12,400 declarations, 679 tagged, 587 contracted, 11,449 untouched, and
zero verified/signed. The raw availability ABI remains integer-valued for C ABI
compatibility; semantic APIs continue to expose `bool`, so no boolean behavior
was replaced by a numeric public workaround.

The engine2d Vulkan dynamic-dispatch module duplicated 24 declarations already
owned by `sffi_vulkan`; it now imports them statically from that owner. All 57
canonical declarations are explicitly FFI-unsafe. Static calls retain the same
direct symbol and dynamic-mode rejection behavior is unchanged, so no runtime
layer, allocation, lookup, or branch was added. Both modules check and lint
without errors. Census: 12,376 declarations, 736 tagged, 587 contracted, 11,368
untouched, zero verified/signed. Existing quarantine arrays still trigger two
unbounded-growth warnings; this slice does not worsen them, and they must gain
backpressure/ownership-aware bounds rather than silently dropping GPU handles.

The general Vulkan facade now statically imports 37 ABI-identical symbols from
the canonical engine2d Vulkan owner and explicitly tags its 37 remaining
graphics-only declarations as FFI-unsafe. This removes duplicate declaration
authority without adding a forwarding wrapper, lookup, allocation, hash, or
call-path branch. The focused check passes and lint has no errors. These tags
do not establish nullability, handle ownership, or signed provider admission.

Dynamic Torch previously redeclared 51 raw symbols beside the canonical Torch
owner. It now statically imports the 39 ABI-compatible symbols and retains only
12 unique or legacy fixed-dimension declarations, each explicitly tagged
FFI-unsafe. The legacy shapes cannot be silently redirected to the canonical
array-descriptor ABI because that would change calling convention. Check and
lint pass; measured check cost was 33.48 seconds / 247,004 KiB peak RSS and
lint was 24.21 seconds / 401,252 KiB with the bootstrap seed. The refreshed
census is 12,300 declaration rows, 785 unsafe-tagged, 587 contracted, 11,243
untouched, and zero evidence-verified, signature-verified, or verified-and-
signed rows. The `rt_torch` family is 167 rows with 139 tagged and 28
untouched. Existing high-level dynamic Torch functions still fabricate zero
for several unavailable/error paths; this consolidation does not call those
APIs safe and the next semantic migration must add typed result/status APIs.

The first dynamic Torch semantic migration removes
`dyn_torch_tensor_linalg_solve -> i64`, which previously collapsed unavailable,
invalid-input, and provider failure into handle zero. Both production consumers
now call `dyn_torch_tensor_linalg_solve_result` and require `status == "ready"`
plus a positive handle before constructing an array. Input handles are released
before error propagation exactly as before. The success path still performs one
raw provider call and one combined status/handle branch; there is no added
lookup, allocation, hashing, or second FFI call. The readiness spec passes 4/4,
all three changed source files check, and lint reports zero errors. The raw C++
ABI still returns a zero sentinel and remains unsigned/unverified, so provider
status/out migration is still required before the Torch boundary is safe.

Dynamic Torch clone, matmul, dot, and inverse now return
`Result<i64, text>` and no longer expose APIs that fabricate handle zero on
provider absence, invalid input, or a null/sentinel provider return. All five
production call sites match the result before constructing or copying a tensor;
resource cleanup remains explicit on error. Each success path performs the same
availability query and exactly one raw operation call as before, followed by a
required positive-handle check. It adds no dynamic lookup, hash, I/O, retry,
second provider call, or explicit allocation. The readiness spec passes 5/5,
three source checks pass, and lint has zero errors. Static string-literal error
reasons avoid inventing numeric boolean/status workarounds. The raw provider is
still unsigned and exception/status-out hardening remains open.

Dynamic Torch now preserves failures for fourteen additional tensor-returning
operations: add/sub/mul/div scalar, pow, relu, sigmoid, tanh, gelu, sqrt, exp,
log, neg, and abs. Their old zero-handle APIs are removed and both the shared
unary dispatcher and scalar dispatcher carry `Result<i64, text>` until the
owning `BackendError` conversion. The five remaining trigonometric helpers are
still legacy internally, but their caller rejects non-positive handles before
lifting. The readiness spec passes 7/7, three focused source checks pass, and
lint has zero errors. A mechanical call-shape audit confirms exactly one raw
operation call and zero explicit allocations in each of the fourteen migrated
wrappers. Required availability/input/output checks remain; no hashing, lookup,
I/O, retry, or extra provider call was introduced.

The dynamic Torch trigonometric family now returns typed results for sin, cos,
tan, asin, acos, and atan2. Production unary and binary dispatchers propagate
the provider reason rather than receiving handle zero. Six duplicate raw
declarations were removed and replaced with compile-time imports from the
canonical tagged Torch owner; there is no runtime forwarding layer. The status
spec passes 4/4, three focused checks pass, lint has zero errors, and the safety
ratchet passes. Census: 12,294 declaration rows, 785 tagged, 587 contracted,
11,237 untouched, and zero verified/signed. `rt_torch` is 161 rows, 139 tagged,
22 untouched. Each result wrapper still has one raw operation call and only
the availability/input/output contract branches.

Dynamic Torch tensor construction and value-copy no longer expose legacy
wrappers that discard explicit status into handle zero or an empty array.
Backend algebra and `TorchNDArray` now consume the existing result structs,
validate `ready` plus handle/length, preserve cleanup on every error path, and
include the provider reason in `BackendError`. This removes a compatibility
wrapper from each success path; it does not add a provider call, allocation,
lookup, hash, retry, or I/O. The status spec remains 4/4, all three production
modules check, and lint has zero errors. Empty arrays can again be legitimate
data only when accompanied by `ready`, rather than doubling as bridge failure.

Dynamic Torch contiguous, squeeze, unsqueeze, and slice now return typed
results and no longer expose zero-handle compatibility APIs. `TorchNDArray`
propagates provider reasons, and two-stage 2-D slicing frees the intermediate
row handle before matching the second result. Readiness passes 8/8, both source
checks pass, and lint has zero errors. Each operation keeps one availability
query and one raw operation call; the second 2-D slice remains intrinsically a
second operation, with no retry, synchronization, lookup, hash, or allocation
added by validation.

Dynamic Torch reshape ranks 1-4 and permute ranks 2-4 now expose only typed
results. `TorchNDArray` matches those results before lifting a handle; transpose
uses the same typed permute path. The status spec passes 5/5, both source checks
pass, and lint has zero errors. Each wrapper contains one availability query,
constant-time input validation, one raw call, and one output-handle check, with
no allocation, lookup, hashing, I/O, retry, or synchronization added.

Dynamic Torch concatenate and stack for two through four inputs now return
typed results, and `TorchNDArray` propagates provider failure reasons instead
of lifting a zero handle. The status spec passes 6/6, both source checks pass,
and lint has zero errors. Existing caller count/shape/device validation remains;
each selected wrapper adds only constant handle checks around one raw operation
call, with no allocation, lookup, hashing, I/O, retry, or synchronization.

Dynamic Torch binary arithmetic and to-float conversion now return typed
results. All production callers propagate provider reasons instead of lifting
zero; conversions release their input handle before matching success or error,
preserving ownership on both paths. Status tests pass 7/7, both source checks
pass, and lint has zero errors. Each wrapper has one raw call and constant input
and output checks only, with no allocation, lookup, hash, I/O, retry, or sync.

Dynamic Torch sum/mean/min/max/argmin/argmax dimension reductions now return
typed tensor-handle results. `TorchNDArray` propagates the reduction reason;
argmin/argmax release the intermediate index tensor before matching the
to-float conversion. Readiness passes 9/9, both source checks pass, and lint has
zero errors. Each simple reduction retains one raw call; arg reductions retain
their intrinsic reduction plus conversion calls, without retries, lookups,
hashing, I/O, synchronization, or added allocations.

Dynamic Torch fixed-dimension zeros, ones, and full constructors for ranks 1-4
now return typed results instead of fabricating handle zero. The tensor owner
matches the result directly and no longer performs a duplicate availability
query before the wrapper. Readiness passes 10/10 and both production modules
check. Each selected path retains one availability query, dimension checks,
one direct raw constructor call, and one handle check; it adds no allocation,
lookup, hash, I/O, retry, or synchronization. The raw provider remains tagged
unsafe and is not signed or evidence-verified.

Dynamic Torch fixed-dimension empty, rand, and randn constructors for ranks
1-4 now use the same typed-result boundary. Their owner dispatcher also removes
its duplicate availability probe. Readiness passes 11/11; each selected path
keeps one availability query and one raw call plus constant dimension/handle
checks, with no added allocation, lookup, hashing, I/O, retry, or sync. These
providers remain unsafe-tagged rather than signed or evidence-verified.

Dynamic Torch eye, arange, and linspace now return typed errors and no longer
fabricate handle zero. `TorchNDArray` removes its duplicate availability probes
and propagates the provider reason before conversion. Readiness passes 12/12;
each constructor retains one availability query, input checks, one direct raw
call, and one handle check, with no added allocation, lookup, hash, I/O, retry,
or synchronization. The raw provider remains unsafe-tagged and unverified.

Dynamic Torch softmax, log-softmax, and leaky ReLU now return typed errors
through `TorchNDArray` instead of fabricating handle zero. Readiness passes
13/13. Each path keeps one availability query, one direct raw call, and
constant input/output checks with no allocation, lookup, hashing, I/O, retry,
or synchronization added. The foreign implementations remain unsafe-tagged.

The authoritative static census now distinguishes unsafe declarations whose
unsafe surface has been minimized (both an unsafe tag and a documented
contract) from unminimized unsafe declarations, and reports verified/signed
counts per family and scope. Current owned-code totals are 12,294 declaration
rows and 3,167 distinct symbols: 12,294 unsafe, 327 unsafe-minimized, 11,967
unsafe-unminimized, 11,237 untouched, and zero evidence-verified, signed, or
admitted. Implementations found by language are Simple 558, Rust 2,161, C
2,323, and C++ 211. These are static source statistics, not safety proof.

Twelve raw dynamic Torch handle declarations now document the exact
nonpositive-handle sentinel enforced by their typed wrappers. This moves them
from tagged-only to unsafe-minimized without claiming provider verification:
`rt_torch` remains 161 unsafe rows, now with 12 contract-documented/minimized,
22 untouched, and zero verified or signed. Scalar floating-point reductions
remain uncontracted because valid zero is still indistinguishable from error.

The remaining dynamic Torch declaration audit removed seven duplicate or
nonexistent raw declarations. GPU memory now aliases the canonical CUDA, CPU,
free, and clone owners; dynamic tensor copying imports the canonical numel and
copy functions; binary arithmetic dispatches directly to the four implemented
providers instead of declaring the missing generic symbol. Fifteen remaining
raw boundaries are explicitly tagged, but this is unsafe-surface minimization,
not provider proof. Tensor copying now rejects an unexpected element count,
guards `n * sizeof(f32)` overflow, and rejects partial copies before allocating
the result array or reading the buffer. The success path retains one provider
copy, one buffer allocation/free, and the existing result construction.

The refreshed owned-code census is 12,287 declaration rows and 3,162 distinct
symbols: 800 unsafe-tagged, 614 contract-documented, 342 unsafe-minimized,
11,945 unsafe-unminimized, 11,215 untouched, and zero evidence-verified,
signed, or admitted. Scalar Torch reductions still require a cross-lane
status/out ABI; valid `0.0` must remain data, never an error workaround.

Eight versioned-in-place checked Torch scalar entrypoints now use an explicit
`i32` status plus `double*` output for sum, mean, min, max, norm, determinant,
standard deviation, and variance. The C++ adapter validates the output pointer
and tensor handle, catches every exception, and writes output only after the
single reduction succeeds. It performs no error reporting, allocation, I/O,
retry, or synchronization. Dynamic Simple callers use a native stack `f64` and
return `Result<f64, text>`; valid zero and NaN remain data. Interpreter handlers
use `MaybeUninit<f64>` and cache each typed symbol with `OnceLock`, eliminating
the old per-call `CString`/`dlsym` path for these checked functions. JIT/native
signature metadata records `(i64, pointer) -> i32`.

The focused readiness spec passes 15/15, both live dynamic callers check, the
C/C++ header parses in both modes, and the new static hot-path contract gate
passes for all eight operations. The compiler crate check remains obstructed by
the unrelated pre-existing missing `interpreter::dispatch_profile` module;
the runtime-symbol ABI unit test passes. Legacy bare-`f64` exports and static
Torch trait consumers remain explicitly unsafe compatibility surfaces and must
still migrate before the family can be called safe or verified.

The refreshed census is 12,295 declaration rows and 3,170 distinct symbols:
808 unsafe-tagged, 622 contract-documented, 350 unsafe-minimized, 11,945
unsafe-unminimized, 11,215 untouched, and zero evidence-verified, signed, or
admitted. `rt_torch` has 162 unsafe rows, 35 minimized, zero untouched, and zero
verified/signed; “zero untouched” means inventoried/tagged, not proven safe.
