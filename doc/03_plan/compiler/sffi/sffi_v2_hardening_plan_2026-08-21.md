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
- 14,398 declaration sites;
- 13,598 sites have neither an explicit FFI-unsafe tag nor a local contract;
- 521 sites declare a typed/documented contract but lack the unsafe tag;
- 259 declarations now carry explicit FFI authority
  but still require canonical ABI-contract metadata;
- 20 checked declarations carry both explicit FFI authority and a
  typed result contract; their cryptographic artifact evidence remains open;
- 399 canonical symbols currently have more than one normalized source
  declaration shape and require typed lowering before one ABI hash can be
  compared; this count is not itself proof of an ABI conflict;
- 3,546 declared symbols require migration and 399 have source-signature
  variants requiring compiler-resolved review;
- among `rt_*`/`spl_*` declarations, 1,715 sites reference symbols classified
  genuinely missing and 318 are backed only in owned C runtime source;
- the distinct-symbol backing census now classifies 699 symbols in the typed
  interpreter registry and 1,189 as genuinely missing.

The inventory tools now fall back to the repository `bin/simple` when no
release-path executable exists, so a missing deployment layout cannot suppress
the census. Source evidence annotations are reported only as
`claim_present_unverified`; no declaration or symbol can become
`declared_complete` without cryptographic verification outside this source
scanner. Monotonic gates reject growth beyond 399 signature conflicts, 3,546
migration-required symbols, or 20,976 raw call sites lacking lexical FFI
authority. These ceilings describe debt, not acceptance: the end state remains
zero, and the generated declaration and symbol ledgers are refreshed in
`doc/08_tracking/bug/data/` on every baseline change.

The ledger names these hashes `source_signature_sha256` and reports
`source_signature_variants`, not `signature_conflict`. High-level `text`, raw
`(ptr,len)`, managed `RuntimeValue`, and local `@extern` adapters can legitimately
spell the same lowered ABI differently. Only compiler-resolved contract metadata
may diagnose an ABI mismatch; the source ledger is a routing inventory.

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

The generated Rust runtime symbol table no longer redeclares the overlapping
memory and time providers with a fabricated zero-argument ABI. The generator
emits their canonical pointer, integer, and return signatures, eliminating all
14 `clashing_extern_declarations` warnings while retaining the same static
address table and lookup behavior. A focused runtime test resolves and invokes
allocation, typed write/read/free, and all three time providers through the
table. This migration adds no runtime allocation, hashing, locking, or lookup.

The runtime build generator now consumes the compiler-owned `RUNTIME_FUNCS`
signature registry rather than inventing `fn()` for every covered linker
anchor. A dependency-free build-time scanner validates the four canonical ABI
scalar types, rejects duplicates/unknown types, and currently parses at least
1,250 contracts (1,264 at implementation time). Exact pointer signatures take
precedence where the coarse codegen registry represents pointers as `I64`.
Legacy multi-value networking tuples remain explicitly marked as improper C
types and require status/out migration; their actual tuple signature is no
longer hidden by a zero-argument declaration. All work is compile/admission
time and leaves the static table and foreign-call hot paths unchanged.

A zero-runtime-cost coverage gate now compares all 1,790 runtime symbol names
with the compiler ABI registry and rejects new uncontracted symbols or lost
coverage. The initial 1,009/781 covered/uncontracted baseline moved to
1,015/775 by migrating all six arena functions. This census parses only actual
list entries, so quoted comments cannot fabricate symbols.

The arena migration also fixed a live ABI mismatch: Simple declared
`rt_arena_alloc(handle, size)` while Rust consumed `(handle, size, align)`.
Simple now passes an explicit alignment of eight and scopes raw calls under
`unsafe(ffi, raw_ptr)`. Rust rejects non-positive capacity, negative sizes,
zero/non-power-of-two alignment, overflow, allocation failure, and poisoned
registry locks without unwinding across the ABI. The bump wrapper now obtains
the arena's actual base allocation rather than treating an opaque handle as a
pointer. Its per-allocation path remains local pointer arithmetic; the raw arena
allocation path retains exactly one existing registry lock and adds no lookup,
hashing, or allocation. Twelve focused arena tests pass. The legacy Simple file
check remains blocked by six pre-existing direct `rt_pool_*` ownership errors
outside this arena family.

Four AES block bridges now have compiler-owned ABI contracts, moving coverage
to 1,019/771. Their native payload-only exports are explicitly Rust-unsafe and
the migrated debug Simple declaration uses lexical `unsafe(ffi)` authority. Interpreter AES
failures now return `CompileError` instead of an empty array or a fabricated
all-zero block; focused tests prove malformed-length refusal and the successful
FIPS-197 AES-128 zero vector. The AES round/block algorithm and successful hot
path are unchanged—no lookup, lock, hashing, or extra allocation was added.
The legacy native payload-only functions still encode failure as an empty
runtime array internally and therefore remain unsafe; checked status/payload
replacements are required before they can back a safe Simple API.
The NVFS vendored AES copy still directly declares the status/out helper; its
own header requires replacement by the canonical pure-Simple module rather
than local edits. That replacement needs an NVFS crypto throughput comparison
before landing so hardening does not silently regress storage performance.

All 30 RuntimeValue/opaque-handle atomic symbols now have compiler-owned ABI
contracts, moving coverage to 1,049/741. The build generator has exact overrides
for Rust `bool` parameters/results and the compare-exchange output pointer, so
the coarse `I8`/`I64` codegen representation cannot create a clashing extern
declaration. A generated-table test invokes integer new/fetch-add/load/free and
boolean new/swap/free successfully. This change is metadata-only for execution:
it adds no wrapper, branch, allocation, lock, lookup, or memory-ordering change.
The opaque-handle implementation still uses registry locks and returns zero or
false for stale handles; therefore the current safe-looking Simple wrappers are
not yet verified lock-free or fail-closed and need a separate API/ownership
migration before critical-mode approval.

The 22 implemented RSA, RSA-PSS, Ed25519, and ECDSA P-256 sign/verify symbols
now have compiler-owned ABI contracts, moving coverage to 1,071/719. The
generated static table is tested to resolve representative checked RSA verify,
Ed25519 verify, and ECDSA sign names to their exact provider addresses. Existing
checked transports retain their tri-state verification and status/payload
semantics; legacy payload-only entries remain compatibility-only. This is
build-time metadata and provider-identity validation only, adding no per-call
lookup, hashing, allocation, lock, or crypto operation.

The three previously uncovered implemented TLS 1.3 AES-GCM payload providers
now have ABI contracts, moving coverage to 1,074/716. All four AES-128/AES-256
TLS payload exports are explicitly Rust-unsafe because their legacy raw ABI
still uses empty arrays for invalid native input. Interpreter encryption and
decryption now return `CompileError` for invalid shapes rather than fabricating
an empty result; authentication mismatch remains `[0]` and successful decrypt
remains `[1, plaintext...]`, including valid empty plaintext. Three focused AES
bridge tests pass and the runtime symbol-table build is warning-free. No AES,
GHASH, allocation, or valid-path control flow changed, so this adds no runtime
cost. The remaining 16 `rt_tls13_*` names have no runtime provider definition
in the inspected Rust/C tree and are not falsely promoted merely because an
interpreter helper or symbol-list entry exists.

The four raw file-mapping lifecycle providers now have exact compiler-owned
pointer/u64 ABI contracts, moving coverage to 1,078/712. This removes the
legacy Simple declaration's 32-bit truncation of mapping lengths and offsets,
honors the caller's mapping-address hint, and makes the raw declarations and
Rust exports explicitly unsafe. The provider rejects null lifecycle pointers,
zero lengths, invalid descriptors, and target-width overflow before entering
the OS syscall. Four focused lifecycle tests, the legacy Simple file check, and
the generated runtime-symbol-table build pass. The syscall hot path gained only
constant-time boundary branches: no allocation, hashing, locking, registry
lookup, dynamic symbol lookup, or per-byte work was introduced.

The file-lock pair now has exact expanded-text and owned-descriptor contracts,
moving coverage to 1,080/710. The Rust runtime no longer exports a one-argument
stub that always returned handle `1` and an unlock stub that always returned
`true`: Unix builds now use `open` plus `flock`, return the actual owned file
descriptor, close it exactly once on unlock, and fail closed for invalid paths,
handles, contention, syscall errors, and unsupported Rust-provider targets.
The compiler generator, Rust declaration generator, and both legacy LLVM
declaration tables agree on `(ptr, len, timeout) -> i64` and `i64 -> bool`.
Raw Simple declarations are tagged `unsafe(ffi)` and the database compatibility
wrapper no longer misdeclares handles as text. Focused lifecycle/contention and
static-provider identity tests cover the boundary. Acquisition performs the
unavoidable path-to-C-string conversion and OS calls; it adds no handle map,
mutex, hashing, dynamic lookup, or work to unrelated file operations.

A new checked offset-read provider moves coverage to 1,081/710 while leaving
the incompatible legacy raw-C-string symbol explicitly unsafe compatibility.
Rust, interpreter, and native-C providers now expose managed optional text:
`nil` means invalid path/offset/size, allocation failure, open/seek/read failure,
while a distinct allocated empty text represents a successful zero-byte or EOF
read. The live process-output relay lifts that optional into
`Result<text,text>` and reports failure instead of silently treating it as no
new output. Focused Rust/interpreter tests prove the empty/failure distinction,
and generated dispatch is bound to the exact provider. The successful path
retains one bounded read and the managed text construction already required by
the caller; it adds no status-array allocation, registry, hashing, locking,
dynamic symbol lookup, whole-file reread, or per-byte validation pass.

All Simple application/library declarations of the ambiguous legacy
`rt_file_read_text_at` symbol are now removed. The canonical file API exposes
`Result<text,text>` over the checked optional transport; enterprise-store reads
propagate failure before parsing or rewriting; SimpleOS exports the same
empty-versus-failure contract with overflow-safe clamping; multipart HTTP range
failure becomes HTTP 500 rather than a corrupt 206 response. The single-range
HTTP path no longer eagerly reads data that its existing bounded body-file
route streams afterward, removing an allocation and duplicate I/O. The raw
C-string-returning compatibility exports remain outside safe Simple code and
need a later ABI removal/release-ownership migration; the guard now prevents
their reintroduction as safe-looking Simple extern declarations.
Test-runner capture now also returns `Result` and converts capture failure into
a failed process result; it cannot turn an unreadable output file into empty
stdout/stderr that might support a false pass. Source checks for every migrated
module pass. The focused source-contract SSpec reaches 13/14 examples: its SFFI
bounded-read assertion passes, while a pre-existing timeout-diagnostic substring
assertion fails outside this change. The deployed `bin/simple` is still the
Rust bootstrap seed and does not contain the newly added checked symbol, so the
runtime behavior SSpec must be rerun after the pure-Simple binary is rebuilt.

The compiler-owned runtime coverage gate now optionally emits the exact missing
symbol ledger atomically, so remediation can target real metadata gaps instead
of treating source spelling variants as ABI evidence. Exact contracts for the
hardened path-mapping pair and SimpleOS Ed25519 seed signer move coverage to
1,084/707. The Ed25519 provider ABI is now consistently three runtime values
(seed, public key, message) on x86_32, x86_64, ARM32, ARM64, and RISC-V; the
previous shared two-argument implementation could misread registers when
called from the canonical Simple declaration. Raw signing is `unsafe(ffi)` and
nullable, all provider failures return nil rather than an empty signature, and
the safe wrapper lifts the boundary to `Result<[u8], text>`. SSH disconnects on
that error. Successful signing retains the same fixed-size inputs, one direct
call, and 64-byte output construction; no lookup, hashing pass, allocation,
lock, or dynamic dispatch was added beyond the cryptographic work already
required.

The four raw integer function-pointer bridges now have exact compiler-owned
ABIs, moving coverage to 1,088/703. Null or negative addresses are runtime
errors in the interpreter and process-fatal contract violations in native C;
they can no longer become a legitimate integer zero. Legitimate foreign zero
returns remain distinguishable and are covered alongside all four arities.
The compatibility loader no longer maintains a fabricated byte-array address
space or returns zero without executing code: it maps RW, bulk-copies packed
code in one SFFI call, transitions RW->RX, and invokes the admitted address.
Raw declarations and indirect-call wrappers carry `ffi`/`raw_ptr` authority,
while module and join-point consumers contain that authority in narrow scopes
and return `Result`. The interpreter call helper now uses fixed stack arrays
instead of allocating a `Vec` per call. A live join-point positive control
executed mapped unadvised and advised targets from the same call site. The
compiled hot path remains a null comparison plus one direct indirect call;
there is no registry lookup, allocation, lock, hash, or generic marshalling.

## Signed evidence admission checkpoint — 2026-08-22

Completed:

- Replace caller-trusted admission booleans with provider-scoped Ed25519
  verification against an independently provisioned trust store.
- Bind admissions to exact artifact, canonical source snapshot, build input,
  compiler, ABI registry, structured passing verification report, symbol, and
  source-signature hashes.
- Reject noncanonical manifests/trust stores, stale or failed reports, tampered
  artifacts, duplicate trust entries, untrusted keys, and substituted
  signatures through a permanent contract test.
- Keep all digest/signature work in the one-time audit/admission path; runtime
  SFFI calls are unchanged.
- Remove one unnecessary parse-shard raw exit and contract/tag the three
  remaining slim-lane raw boundaries without reintroducing the 3.3 GB broad
  compiler closure.

Next:

1. Define production provider evidence packages and provision non-test trust
   anchors; the normal census must remain at zero admissions until this exists.
2. Generate ABI registry rows from compiler-owned resolved signatures rather
   than handwritten manifests.
3. Add target/binary-format identity checks to loader admission and publish
   immutable typed function slots only after whole-provider validation.
4. Continue reducing the 11,836 untouched rows by owner/facade family, starting
   with the 999 untouched `rt_process` declarations.

Scope-aware prioritization is now available. The next owner sweep should use
the 5,718 untouched production rows as its primary queue while independently
ratcheting 655 bootstrap-library and 5,463 test rows. The complete 12,614-row
total remains authoritative; scope is a prioritization dimension, not an
exclusion or a safety claim. Current top untouched production families are
`rt_file` (560), `rt_cuda` (256), `rt_torch` (205), `rt_env` (165), and
`rt_vulkan` (156). Prefer canonical owners for file/environment families and
explicit unsafe generated bindings for accelerator families.

The raw-access lint now treats exact lexical FFI containment as the accepted
fallback when importing a semantic facade would violate a measured closure or
latency constraint. This does not classify the call as verified or safe: it
only distinguishes reviewed unsafe containment from accidental raw access.
Next lint work must fix the pre-existing process-run auto-fix scope bug without
inventing nullable file/env rewrites, then ratchet uncontained production calls.

The first `rt_file` slice now has a nullable raw contract and a checked
`file_read_result` facade. Before migrating the remaining production file-read
declarations, rebuild the deployed Simple tool and run one contract fixture in
interpreter, JIT, native, and sealed-dynload lanes. Do not bulk-rename callers:
migrate semantic owners to the checked facade and measure closure, latency, and
RSS at each owner boundary.

The first unused-boundary sweep removed 66 dead `rt_file_read_text`
declarations without changing any call path. Continue this exact-occurrence
cleanup for other `rt_file` symbols before tagging: deletion is safer and
cheaper than granting unused declarations FFI authority. For live declarations,
migrate callers to canonical checked owners; tag only irreducible raw bindings.
The current gate is 12,548 declarations, 11,770 untouched, and zero signed
admissions. Do not claim safety until provider evidence is admitted and the
cross-lane nullable-read deployment gate passes.

The all-symbol unused `rt_file_*` sweep removed a further 33 dead boundaries;
the current gate is 12,517 declarations and 11,741 untouched. The next file-I/O
work must target live duplicate declarations: route ordinary callers through
the canonical checked facade, retain direct raw calls only where measured
closure constraints require lexical `unsafe(ffi)`, and avoid per-call registry,
signature, or hash work. Signed admission remains a load-time operation and is
still zero for production providers.

Five modules now route live raw text reads through the canonical facade. Improve
the unused-boundary audit so comment-only mentions do not hide dead declarations,
then repeat deletion before migrating additional live callers. Preserve the
file-I/O-dominated hot-path shape: one typed call and required null/result branch,
with signature/evidence verification confined to provider admission.

The canonical `file_exists` owner is now tagged, contract-documented, and
lexically contained; six duplicate application wrappers were removed. Continue
the same owner-first migration for live existence predicates, but preserve
specialized no-follow, sandbox, and loader admission semantics rather than
rewriting them to the general boolean facade. Current gate: 12,506 declarations,
11,729 untouched, zero signed admissions.

The plugin and wrapper-generator owners now use compile-time aliases for the
canonical text-read facade, removing three raw declarations without increasing
call depth. Continue alias-based consolidation where local wrappers are exact
pass-throughs; retain semantic adapters where error or ownership behavior differs.

The canonical write and recursive-directory-create boundaries are now tagged,
contracted, lexically contained, and no longer exported raw for production use.
Next migrate the remaining raw read export consumers in tests to the canonical
facade, then remove that export; do not alter source-content assertions while
changing the transport owner.
