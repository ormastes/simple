# SFFI v2 Hardening Implementation Plan

**Date:** 2026-08-21

**Research:** `doc/01_research/platform/sffi_v2_hardening_2026-08-21.md`

**Requirements:** `doc/02_requirements/feature/sffi_v2_hardening.md` and
`doc/02_requirements/nfr/sffi_v2_hardening.md`

**Architecture/design:** `doc/04_architecture/platform/sffi_v2_hardening.md`
and `doc/05_design/platform/sffi_v2_hardening.md`

**Status:** Planned; no implementation or verification PASS is claimed

## Objective

Make every foreign boundary fail closed and consistent across the Rust seed,
self-hosted interpreter, JIT, native/AOT, sealed dynload, test runner, and
SimpleOS. A foreign call may produce only a contract-valid typed value,
`Option.None`, `Result.Err`, or a provider/module admission error.

## Frozen shared interfaces

Before parallel implementation, the merge owner freezes:

- `SffiFunctionContractV2` and canonical type IDs;
- `SffiError` diagnostic codes;
- return families, ownership, allocator, unwind, callback, and thread policies;
- canonical ABI hash encoding;
- provider registry C ABI;
- source/evidence hash encoding and trust policy;
- cross-lane conformance fixture format.

No lane may create a private duplicate registry, ABI encoder, error enum, or
contract meaning.

## P0 — Fail closed

Normative requirements: `REQ-SFFI-V2-001` through `REQ-SFFI-V2-012`.

Principal paths:

- `src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs`
- `src/compiler_rust/compiler/src/interpreter_call/core/macros.rs`
- `src/compiler_rust/compiler/src/interpreter_extern/`
- native linker/runtime and SimpleOS extern-closure owners
- test-runner verdict owners

Work:

1. Represent body fallthrough as a return origin, not `Value::Nil`.
2. Replace the unit-only final guard with total return-contract validation.
3. Reject optional fallthrough in hardened/critical profiles unless `nil` is
   explicitly returned.
4. Make unsupported dynamic values, missing symbols, and null function pointers
   typed errors.
5. Remove the all-`i64` dispatcher from hardened/critical execution.
6. Remove weak empty/zero/nil production providers and linker substitutes.
7. Make skipped, unsupported, or provider-missing SFFI tests non-passing states.
8. Add sabotage fixtures for missing symbol, null-on-success, invalid sentinel,
   malformed descriptor, and missing return.

Exit gate: no scoped lane can fabricate a usable default, and every negative
fixture reports the canonical error category exactly once.

## P1 — Canonical typed contracts and lift wrappers

Normative requirements: `REQ-SFFI-V2-101` through `REQ-SFFI-V2-112` and
`REQ-SFFI-V2-NFR-001` through `REQ-SFFI-V2-NFR-006`.

Principal paths:

- `src/compiler/00.common/sffi/`
- frontend attributes under `src/compiler/10.frontend/`
- HIR under `src/compiler/20.hir/`
- semantics/safety under `src/compiler/35.semantics/`
- `src/compiler/90.tools/sffi_gen/`
- Rust seed parser/HIR mirrors

Work:

1. Add `SffiFunctionContractV2` and deterministic contract IDs/ABI hashes.
2. Admit only fixed-width scalars, explicit `repr(C)` layouts, opaque pointers,
   status values, and versioned descriptors at the raw ABI.
3. Model nullable, status/out, sentinel, tagged result, ownership, allocator,
   span, callback, unwind, and thread contracts.
4. Add `ForeignRaw<T>` or an equivalent HIR validation state that cannot be
   dereferenced, exported, or stored safely before lifting.
5. Generate C headers, C++ exception shims, Rust C-ABI shims, raw Simple
   declarations, safe Simple wrappers, provider registries, and documentation
   from the same registry.

Exit gate: one contract edit deterministically regenerates every consumer; no
handwritten name-only duplicate registry is required.

## P2 — Lexical safety and assurance profiles

1. Lower every raw extern call to one `HirCall.SffiRaw(contract_id)` operation.
2. Attach and enforce `UnsafeCapability.Ffi` in seed and self-hosted compilers.
3. Preserve contract/effect metadata through macros and aspect weaving, then
   rerun type/safety checks after weaving.
4. Enforce profiles:
   - normal: unverified providers are unsafe-only;
   - hardened: signed plus runtime-checked for generated safe wrappers;
   - critical: static or sealed-complete provider with approved evidence,
     trusted TCB status, or isolation.

Exit gate: the same raw-call-negative fixture fails before backend selection in
every compiler stage.

## P3 — Typed thunks and provider admission

1. Define and emit the versioned provider registry C ABI.
2. Parse registry metadata without executing arbitrary provider initializers
   where the platform permits detached metadata/sections.
3. Validate provider, target, registry, and per-symbol ABI hashes.
4. Resolve every required symbol before entry and publish immutable typed slots
   atomically.
5. Track provider generation/revocation for borrowed resources and callbacks.
6. Keep a complete descriptor/libffi fallback explicit-unsafe, development-only,
   and unavailable in critical mode.

Exit gate: sealed dynamic call assembly performs no symbol-name lookup, hashing,
generic decoding, or allocation per scalar/opaque-handle call.

## P4 — Cryptographic evidence admission

**Status: planned, not implemented or verified by the P0/P1 documentation set.**

Principal owners include assurance stamps, artifact manifests, mission-critical
evidence modules, build/release scripts, and SimpleOS loader trust policy.

1. Implement versioned canonical source-tree SHA-256 with text-only CRLF/lone-CR
   normalization and length-framed path/content encoding.
2. Compute exact build-input, compiler/linker/code-generator/dependency, ABI
   registry, verification report, and artifact SHA-256 identities.
3. Define canonical `SffiEvidenceManifestV1` encoding.
4. Add structured Ed25519/offline and Sigstore-style/online signature adapters,
   trusted key identities, validity, and revocation policy.
5. Verify artifact, signature, target/profile, provenance, ABI registry, required
   receipts, and symbols before atomic publication.
6. Cache admission only by exact artifact, provider, target, profile, and registry
   identities.

Exit gate: LF/CRLF text checkouts share canonical source identity, while any
meaningful source, compiler, flag, dependency, registry, receipt, or artifact
change invalidates stale evidence.

## P5 — Provider migration

**Status: planned after P0/P1 contracts and P2/P3 enforcement/admission.**

Migrate in this risk order:

1. unknown/unregistered externs and fabricated return paths;
2. signature, verification, hashing, loader, process, and filesystem APIs;
3. resource create/destroy and allocator-sensitive text/array bridges;
4. database, network, TLS, crypto, GPU, driver, and UI providers;
5. callbacks, async completion, variadics, and platform-specific APIs;
6. low-risk pure scalar providers.

For each provider: inventory a pure-Simple counterpart first, define the
contract, generate shim/wrapper, attach analyzer/sanitizer/fuzz/proof evidence,
run cross-lane tests, benchmark, then remove the legacy binding. Raw declarations
remain internal and are never re-exported as safe APIs.

### Checked generic-transport transition

Add checked raw transports alongside—not in place of—the legacy value-returning
ABI:

```text
spl_wffi_try_call_i64(fptr, args, nargs, out) -> transport_status
spl_wffi_try_call_f64(fptr, args, nargs, out) -> transport_status
spl_wffi_try_call_i64_with_bytes(..., out) -> transport_status
```

On status zero, `out[0]` contains the foreign return unchanged, including a
legitimate `0`, `0.0`, or `-1`. Nonzero status represents only bridge rejection
such as a null function pointer, invalid arity, or malformed descriptor. Add
native exports first, interpreter parity second, canonical no-GC `Result`
wrappers third, then migrate the single with-bytes caller, plugins, and each
LLVM/font/T32/GPU contract family separately.

At `try_call_dynamic`, generic dispatch also requires explicit development-only
legacy opt-in. Robust, critical, verified, their aliases, and unknown profiles
deny with `E-SFFI-014` before `dlopen`/`dlsym`. Replace this temporary serialized
profile seam with typed policy carriage when the frozen registry reaches the
Rust interpreter.

## P6 — Conformance and performance gates

**Status: planned; focused P0/P1 reproduce-first evidence does not constitute
the complete P6 matrix.**

Run each supported fixture under seed interpreter, self-hosted interpreter,
`simple test`, `simple run`/JIT, native/AOT, sealed dynload, SimpleOS, Linux, and
Windows. Required sabotage includes:

- missing/duplicate symbol and wrong ABI hash/layout/calling convention;
- null-on-success, failure-with-live-output, zero/negative sentinels;
- invalid pointer/length/capacity and invalid UTF-8;
- allocator mismatch, missing destructor, callback after release;
- C++ exception and Rust panic crossing a forbidden boundary;
- modified artifact, compiler, flag, dependency, manifest, signature, or proof;
- stale admission cache and provider revocation;
- legitimate empty data remaining distinct from bridge failure.

Performance evidence compares direct C, a correct handwritten checked wrapper,
generated static wrapper, sealed typed slot, and unsafe generic fallback. Report
cycles, branches/mispredictions, allocations, code size, admission time, retained
cache memory, and assembly shape. Boundary status/null checks remain enabled by
default, including critical/release builds.

## Parallel ownership

| Lane | Owner scope | Acceptance |
|---|---|---|
| A0 | shared schema, errors, encodings | frozen golden vectors and compatibility policy |
| A1 | Rust seed return/interpreter extern semantics | no fallthrough/default fabrication |
| A2 | self-hosted frontend/HIR/safety | lexical `unsafe(ffi)` parity |
| A3 | C/C++ generation | stable C ABI, exception barrier, no C++ ABI leakage |
| A4 | Rust generation | checked `NonNull` lift, C-compatible exports, panic policy |
| A5 | JIT/native/linker/SimpleOS | complete closure and atomic typed slots |
| A6 | hashing/provenance/signing | golden hashes and tamper rejection |
| A7 | conformance/sabotage/performance | cross-lane category parity and hot-path evidence |

Sidecar lanes are planned for implementation only; none ran for this
document-preservation commit. Merge owner and final highest-capability reviewer:
`/root` unless reassigned before implementation.

Integration order:

```text
A0 schema freeze
 -> A1 + A2 + A3 + A4
 -> A5 typed closure/admission
 -> A6 exact evidence binding
 -> A7 final cross-lane gate
```

## Diagnostics

Reserve stable codes `E-SFFI-001` through `E-SFFI-020` for unresolved symbol,
unsafe-scope failure, ABI/artifact/signature/evidence mismatch, null/sentinel/
output/descriptor/encoding/ownership/unwind/signature violations, unvalidated
foreign use, missing return, value-bridge corruption, provider revocation,
duplicate symbol, and critical-profile rejection. Tests assert codes, not prose.

## Stop criteria

- Verify each acceptance criterion once per session.
- Use no more than three verify/fix cycles per phase.
- Stop at the first converged phase; do not rerun green checks.
- P0 is the minimum prerequisite for any non-null-safe claim.
- Critical readiness requires every phase through P6 plus a separate `$verify`
  `STATUS: PASS`; this plan itself is not verification evidence.

## Current implementation checkpoint — checked C/Rust transport

Completed in the `codex/sffi-v2-full` lane:

- Rust native and interpreter checked integer/byte-descriptor transports;
- argument-array bounds and maximum-arity validation before invocation;
- pure-Simple `DynLib.call_checked -> Result<i64, text>` lifting;
- C status/out `spl_wffi_try_call_i64_c`, including null output/function checks;
- null `dlclose` rejection in both owned C runtime definitions;
- Ed25519 native/interpreter argument-order parity and checked tri-state verify;
- a cross-owner lint guard covering registrations, null checks, and signature
  order, plus focused Rust and C syntax tests.

Next migration checkpoint:

1. migrate every remaining legacy dynamic-call consumer to a typed or checked
   contract family;
2. add checked RSA/ECDSA sign/verify output APIs and route safe Simple callers;
3. replace caller-supplied loader verification booleans with canonical signed
   manifest verification against a trusted-key registry;
4. complete the owned C/C++ provider inventory by ownership/null/status family;
5. run the full P6 cross-lane and release verification matrix.

This checkpoint is an implemented hardening increment, not a claim that every
repository SFFI provider is already robust/critical-safe.

## Full owned-extern inventory checkpoint

`scripts/audit/sffi-contract-inventory.shs` now joins the deployed-binary
backing census with declaration-local unsafe, contract, and evidence markers.
Its generated ledger is
`doc/08_tracking/bug/data/sffi_contract_inventory_2026-08-21.tsv`; the canonical
symbol/signature roll-up is
`doc/08_tracking/bug/data/sffi_contract_symbols_2026-08-21.tsv`.

Current evidence after the checked regex boundary migration:

- 3,963 distinct symbols in the current backing census, including 3,961
  compiler-owned canonical symbols;
- 14,391 declaration sites;
- 13,634 sites have neither an explicit FFI-unsafe tag nor a local contract;
- 508 sites declare a typed/documented contract but lack the unsafe tag;
- 234 declarations now carry explicit FFI authority
  but still require canonical ABI-contract metadata;
- 15 checked declarations carry both explicit FFI authority and a
  typed result contract; their cryptographic artifact evidence remains open;
- 401 canonical symbols currently have more than one normalized declaration
  shape and require typed-resolution review before one ABI hash can be sealed;
- 3,547 declared symbols require migration and 401 require conflict resolution;
- among `rt_*`/`spl_*` declarations, 1,715 sites reference symbols classified
  genuinely missing and 318 are backed only in owned C runtime source;
- the distinct-symbol backing census now classifies 698 symbols in the typed
  interpreter registry and 1,189 as genuinely missing.

The regex wrapper now exposes checked `Result` construction and boolean-match
operations. The interpreter registers all 15 `rt_regex_*` symbols to typed
handlers backed by an O(1), generation-checked slab. Boolean handle calls borrow
their text argument and add no allocation, hashing, dynamic loading, or
string-name lookup. The rebuilt-interpreter regression passes all five examples;
no weak fallback or skipped test was introduced.

The TRACE32 boundary now has one physical implementation owner. Eight sync
`t32_ffi` compatibility modules and eight async `t32_sffi` copies are explicit
re-export facades over `std.nogc_sync_mut.debug.remote.t32_sffi`; this removes
108 duplicate raw declarations and 682 duplicate unauthorised call sites with
no runtime wrapper, allocation, lookup, or code-size duplication. The canonical
TRACE32 declarations and direct-call functions now carry explicit `ffi` and
`raw_ptr` authority and pass robust SFFI lint. The provider remains unverified:
nullability, bounds, ownership, ABI hashes, and signed artifact evidence still
need executable contracts before any safe facade can be published.

The legacy `std.ffi.dynamic` implementation is now an explicit facade over the
canonical `std.sffi.dynamic` owner, removing its divergent missing-symbol
zero fallbacks. The canonical raw loader declarations and direct invocation
methods carry `ffi`/`raw_ptr` authority and pass robust lint. This is a zero-cost
source alias: no wrapper, additional lookup, allocation, or branch is emitted.
The integer-only dispatcher remains unsafe and ineligible for verified/critical
admission until replaced by generated typed thunks bound to signed ABI evidence.

The legacy `std.ffi.llvm_loader` implementation is now an explicit facade over
the canonical `std.sffi.llvm_loader` owner. The canonical raw memory, symbol
resolution, and integer-call declarations and their direct callers carry
`ffi`/`raw_ptr` authority and pass robust SFFI lint. The existing function-pointer
cache and <=8-element scratch buffer are unchanged, and the facade is a source
re-export, so this migration adds no call, allocation, lookup, branch, or hash to
the hot path. The LLVM integer dispatcher remains unsafe and unverified: its
zero sentinel, ABI shape, pointer ownership, and provider artifact have not yet
been admitted by typed contracts and signed evidence.

The legacy `std.ffi.codegen` Cranelift implementation is now an explicit
re-export facade over `std.sffi.codegen`. This removes 400 lines of duplicate
boundary code and 94 duplicate unauthorized raw calls without adding a wrapper,
lookup, allocation, branch, or hash. Its compatibility facade uses the approved
`__init__.spl` re-export-module shape, avoiding a wildcard and the wide-public
lint without changing runtime resolution. All 77 declarations and 75 direct
wrappers in the canonical owner now carry `ffi`/`raw_ptr` authority and pass
robust lint; an annotation-stripped comparison proves the executable bodies are
unchanged. The provider ABI and handle/null contracts are not yet sealed or
bound to signed artifact evidence, so this boundary remains unsafe rather than
verified.

The canonical SDL2 window boundary now tags all 66 raw declarations and only
the 52 functions that directly invoke them with the minimal `ffi` capability;
pure event/value helpers remain safe and no `raw_ptr` capability is granted.
An annotation-stripped comparison proves its executable Simple bodies are
unchanged. The Rust interpreter no longer converts a NULL text result into
successful empty text: because the owned C provider supplies explicit non-null
fallback strings, NULL now produces a typed provider-contract error. A sabotage
test plus the five existing SDL registration/shape tests pass. This adds one
null comparison only on SDL text-return calls; scalar/event paths are unchanged.
The boundary is still not verified or signed, and unrelated pre-existing stub
and wide-public lint findings remain open.

The Rust TLS-client interpreter lift now distinguishes a valid zero-length
runtime string from the corrupt combination `len > 0 && data == NULL`. The
former remains empty text; the latter is a typed provider-contract error rather
than fabricated success. Both focused sabotage/empty-value tests pass. The
success path retains the existing length check, data lookup, and copy and adds
no hashing, lookup, allocation, or branch; error text is allocated only on the
contract-violation path. The null/signature guard now locks both SDL and TLS
fail-closed lifting rules.

The Rust Cranelift interpreter now applies the same descriptor rule to the
`rt_file_hash` text result: zero length remains valid empty text, while positive
length with NULL data is a typed contract error. Its four focused tests pass,
including both descriptor sabotage cases and the existing argument/arity
validation. The success path keeps the prior length/data/copy sequence and adds
no admission work or dynamic lookup.

The Rust audio interpreter now enforces the owned C provider's non-null backend
name contract. NULL becomes a typed contract error rather than empty text; all
five focused audio registration, arity, backend, and sabotage tests pass. The
change adds only the existing-required null comparison on the backend-name
query and does not touch audio processing or scalar hot paths.

The Vulkan, GLFW, and SDL3 interpreter text lifts now reject NULL instead of
manufacturing empty text. Their owned Rust/C providers already encode ordinary
absence with non-null empty/static strings. One combined sabotage run passes
all four matching null-contract tests (including SDL2). The added comparison is
limited to text-return calls; graphics/event/scalar paths are unchanged.

The screenshot interpreter now treats NULL owned-string returns from output-dir
and capture-path queries as typed errors instead of successful empty paths. Its
sabotage test passes, while the successful copy-then-provider-free ownership
path remains unchanged. No new work occurs outside these infrequent getters.

The generic string-builder interpreter finish path no longer maps an invalid
handle (`RuntimeValue::NIL`, length `-1`) or positive-length NULL data to empty
text. Empty builders remain valid empty text. All three focused pointer/length,
invalid-handle, and empty-builder tests pass. The normal positive-length path
retains its existing `len <= 0` and NULL comparisons with no added hot-path
lookup, allocation, or hashing.

The cryptographic signature byte bridge now rejects `RuntimeValue::NIL` before
generic collection decoding and accepts NULL string data only when the declared
length is exactly zero. This prevents NIL or a corrupt positive-length string
from becoming valid empty key/message/signature bytes. All six focused Ed25519,
checked-family, bridge-failure, and empty-value tests pass. Existing non-empty
array/string conversion loops and cryptographic calls are unchanged.

These are migration inputs, not 14,391 independent implementations. The audit
now hashes normalized declaration shapes and groups them by symbol. The next
tooling step replaces the text-derived shape with the resolved HIR ABI hash,
rejects the 401 conflict groups, and converts compatibility modules to
re-export the canonical no-GC owner. Safety is then discharged once per
symbol/ABI hash while every raw call site retains a minimal lexical
`unsafe(ffi)` scope. `SFFI009` rejects raw calls outside such a helper and
`SFFI010` rejects raw declarations without explicit FFI authority in robust
and critical lint profiles; both checks are source-time only. The call lint now
also carries raw `rt_*`/`spl_*` identities imported from modules whose name
contains `sffi`, closing the prior declaration-local blind spot. Imported HTTP
server and web-framework thread calls now use lexical FFI blocks. Those blocks
add no helper dispatch, allocation, lookup, or synchronization to the existing
native call path.

The lint launcher now accepts both `--profile=robust` and `--profile robust`,
normalizes the latter before invoking the engine, and does not misclassify the
tier as an input file. This is command-line setup work only; it does not enter
compiled application or SFFI call paths. Production-launcher verification still
requires redeploying the pure-Simple binary.

The source-driven robust CLI gate now produces a terminal passing JSON verdict
for the migrated HTTP-server and thread-pool modules. Its required-comment
admission prefilter was repaired as a small allocation-free scan over the
dangerous-keyword registry; this affects lint time only and avoids per-keyword
temporary string construction.

`scripts/audit/sffi-call-authority-census.shs` now supplies the scalable raw
call-site migration ledger at
`doc/08_tracking/bug/data/sffi_call_authority_2026-08-21.tsv`. It recognizes
file-local externs and explicit `rt_*`/`spl_*` imports from SFFI modules, tracks
function and lexical FFI authority by indentation, and can fail CI with
`SFFI_FAIL_ON_MISSING=1`. The current source/test census contains 20,990
missing-authority calls, 51 lexical scopes, and 566 function scopes across 3,142
files. It completed in 24.21 seconds at 7,424 KiB maximum RSS. This is a
migration index rather than ABI proof; aliases, generated bindings, and
re-exports still require resolved-HIR identity.

The bare-metal CLI is the first dense production migration selected from this
ledger: its three raw declarations are explicitly FFI-unsafe and all 24 direct
calls now sit in minimal lexical blocks. No helper dispatch was introduced;
the stdout/stderr/exit ABI calls remain direct and the module passes robust
SFFI lint.

The byte-for-byte duplicate `app.io.window_ffi` implementation has been
replaced by an explicit compatibility facade over `app.io.window_sffi`. It
re-exports only safe wrapper types/functions—not raw `rt_sdl2_*` or
`rt_winit_*` symbols—removing 53 duplicate declarations and 59 duplicate raw
calls. Re-export resolution is static, so this consolidation adds no per-call
lookup or wrapper layer. A real three-case compatibility spec replaces the old
always-skipped placeholder.

The identical `app.io.gamepad_ffi` and `app.io.graphics2d_ffi` boundaries are
now explicit safe-surface facades over their canonical `_sffi` owners. Together
they remove another 69 duplicate declarations and 69 duplicate raw calls, do
not export raw provider symbols, and replace two always-skipped legacy specs
with six passing structural cases. These are static re-exports and add no
runtime wrapper or lookup.

The identical `app.io.rapier2d_ffi` and `app.io.tls_ffi` copies are now explicit
safe-surface facades as well. This removes another 83 duplicate declarations
and 73 duplicate raw calls. The TLS facade exposes only validated wrapper
types/functions and no `rt_rustls_*` provider symbol; both facades compile and
their six structural compatibility cases pass. Static re-export resolution
again leaves the foreign-call hot path unchanged.

The app audio pair and its stale app-local `_sffi` subset are consolidated onto
the richer no-GC owner, removing 62 duplicate declarations and 48 duplicate raw
calls while replacing its 568-line skipped legacy spec with four passing facade
assertions. The app paths expose only safe wrappers; generation-counted handle
validation and future evidence now have one owner. SQLite was
deliberately not collapsed in this batch: its pair contains a real placeholder
construction algorithm difference, so performance/semantic equivalence must be
measured before selecting the canonical implementation.

The app compression, FTP, and regex `_ffi` implementations were also redundant
with their existing `_sffi` facades over no-GC owners. They are now explicit
safe-surface compatibility modules, removing 64 duplicate declarations and 65
duplicate raw calls. A shared three-case spec proves the facades contain no
foreign declarations, wildcard exports, or `rt_*` exposure. All three compile;
static resolution preserves their prior call-path cost.

Thread-pool construction no longer treats a zero/invalid native worker handle
as a successfully degraded pool. The unused duplicate thread-create extern was
removed; the remaining spawn ABI is explicitly FFI-unsafe, called in a lexical
block, and fails closed during pool initialization. Task submission and worker
execution hot paths are unchanged.

Performance constraint: the legacy native integer call remains allocation-free.
The lint guard extracts its body and fails if `rt_array_new`, `Vec`, maps,
mutexes, `dlsym`, or other lookup/allocation primitives enter that hot path.
Typed sealed thunks remain the production target; pair-returning checked arrays
are migration/interpreter adapters, not the final critical hot path.

Security-sensitive verification checkpoint: deployed/interpreter transports now
provide tri-state checked results for Ed25519, RSA PKCS#1 SHA-256/SHA-512,
RSA-PSS SHA-256/SHA-384/SHA-512, and ECDSA P-256. Malformed bridge values return
`-1`, a processed invalid signature returns `0`, and a valid signature returns
`1`. Safe Simple wrappers lift those states to `Result<bool, text>`, and the SSH
client host-key path uses the checked dispatcher. P-384/P-521 remain rejected by
that dispatcher until checked providers exist. The additional status branch is
constant-time transport work relative to the existing cryptographic operation;
no registry lookup, hashing, mutex, or wrapper allocation was added.

Checked signature generation now covers RSA PKCS#1 SHA-256/SHA-512, Ed25519,
and ECDSA P-256. Its descriptor carries status plus payload so malformed bridge
input, invalid keys, provider failures, and successful signatures remain
distinct. Legacy entry points retain their original payload-only ABI and do not
allocate the checked descriptor. The Ed25519/ECDSA shared helpers return the
runtime payload directly; a guard rejects temporary `Vec` copies or descriptor
allocation on those legacy paths. The TLS client CertificateVerify Ed25519 path
uses the checked Result wrapper.

Artifact admission now has a canonical `SimpleArtifactManifest` v1 signing
codec. It length-frames the exact image SHA-256 and every manifest policy field,
excludes only the signature container, bounds text/list/total input sizes, and
rejects malformed artifact/content digests. This codec runs only during load
admission; it adds no hashing, lookup, allocation, or branch to an admitted
SFFI call. Loader-owned trusted-key initialization, detached Ed25519 envelope
verification, and authority publication remain fail-closed follow-up work.

The loader now owns a serialized, initialize-once Ed25519 trust-root capsule.
It accepts only the strict `ed25519:<key-id>:<128-hex>` envelope, hashes the
selected public key, compares it with the admission trust-root identity, and
verifies the canonical manifest/image bytes before constructing an executable
handle. Its verification receipt is package-private; caller-provided booleans
remain rejection hints and cannot become authority. The interpreter gained
checked mutex counterparts so the owner capsule does not depend on fabricated
zero/false synchronization results. After successful verification the pipeline
now retrieves the already-initialized loader authority owner and issues the
package-private token for the exact open handle; missing/invalid owner state
still closes the handle and rejects admission. The privileged bounded mapping
consumer remains intentionally blocked. The native fixture compile-cost blocker is recorded
in `doc/08_tracking/bug/sffi_manifest_signature_native_test_compile_cost_2026-08-21.md`.

The raw-SFFI lint now understands lexical `unsafe(capabilities: [ffi])` block
indentation, including value-binding forms, and proves that authority ends when
the block indentation ends. The canonical thread/mutex/condition-variable
declarations are explicitly FFI-unsafe and their wrapper calls use lexical
blocks, avoiding an extra helper call on synchronization hot paths. The current
parser cannot bind an unsafe block expression directly, so two create paths use
a typed local assignment; the optimizer/codegen evidence needed to prove away
that initialization is tracked in
`doc/08_tracking/bug/unsafe_block_expression_binding_parser_gap_2026-08-21.md`.

## Requirement decision

The user selected the recommended SFFI v2 architecture: versioned stable C ABI
shim, generated unsafe raw declaration, generated validation/lift wrapper, and
safe typed API. P0/P1 requirements and NFRs are final in the linked documents.
Detailed P4 signing/trust deployment and P5 migration scheduling remain planned
decisions; they must not delay P0 fail-closed behavior or be claimed complete.

Packed-span resolution now exposes `Result<i64, i64>` instead of allowing the
raw zero sentinel to escape as a usable address. The Simple wrapper performs
one raw resolve and one success comparison; it queries the thread-local verdict
only on failure. Capability-scoped unsafe blocks are parsed by the seed parser,
and all nine packed-span functions are wired into the interpreter's static
dispatch table. The focused parser/registration tests pass and the packed-span
spec passes 25/25, including the one-check-per-batch performance assertion.
