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

Raw read/write exports are now removed. Fix the import-alias dependency-capture
bug before using aliases that reuse foreign symbol names; until then use the
canonical exported name directly. Repair the stale installer-font source
contract separately. Neither issue justifies reopening raw SFFI exports.

The raw-looking shell rename export is removed and all consumers use the typed
canonical rename boundary. Continue auditing general-module `export rt_*`
entries before explicit FFI modules: replace misleading wrappers with semantic
names, remove shell/process marshalling where a typed provider exists, and tag
the irreducible raw declaration at its single owner.

Timestamp and sleep now have semantic exported names, and sleep uses the typed
thread provider rather than shelling out. Continue with general `app.io` debug
and fault-control exports: expose reviewed capability APIs where available and
otherwise keep raw controls in explicitly unsafe modules rather than the broad
compatibility facade.

Database evidence helpers now use real canonical identity/time providers rather
than dummy zero/fixed values. Continue searching production `rt_*` definitions
for constant success, zero, empty, or dummy returns before merely tagging them;
fabricated implementations must be replaced or deleted, not blessed as unsafe.

Live pitch is the first fabricated audio implementation removed: the real C
provider owns generation-handle validation and performs a direct miniaudio
operation, while one safe Simple boolean wrapper owns the raw status lift and
the only lexical `unsafe(ffi)` call. Six unsupported, unused live node-graph
effect boundaries and their constant-zero implementations are deleted rather
than granted unsafe authority. Continue the fabricated-implementation queue
with JIT setters that claim success while ignoring configuration. Preserve this
slice's hot-path rule: existing owner lock plus direct typed call and status
comparison; provider evidence and signatures remain admission-time work.
Current gate: 12,493 declaration rows, 11,711 untouched, 508 tagged, 586
contracted, and zero verified/signed admissions.

The soft JIT backend/optimization fabricated-success setters are fixed. Backend
selection is now an honest constant-time capability check, native availability
is false, optimization level zero is the only accepted level, and integer
execution preserves `-1` through a typed internal result. Fake last-error state
was removed, eliminating its post-call operation. Next inspect the remaining
empty-return paths, especially string execution, and either lift them to a
typed result or delete unsupported APIs; do not introduce file-backed error
state or per-call registries. Current gate: 12,492 declarations, 11,711
untouched, 508 tagged, 585 contracted, and zero verified/signed admissions.

JIT string execution now returns `Result<text, text>` and the raw-looking
empty-on-error implementation is removed. Continue the same rule for other
text/array APIs: preserve legitimate empty values inside `Ok`, represent
absence with `Option`, and represent operational failure with `Err`; do not add
second-pass last-error queries or persistent error maps. The declaration gate
is unchanged at 12,492 rows with zero signed admissions, while Simple `rt_*`
implementations drop to 574 rows (532 distinct symbols).

Dead SDL2 compatibility aliases for winit presentation/redraw and fabricated
scale-factor APIs are removed; borrowed event destruction is unit-valued. Keep
deleting unused compatibility boundaries before tagging them, while retaining
the real Rust winit provider's checked command path and the canonical SDL2
presentation owner. Current census: 12,492 declarations, 11,710 untouched, 508
tagged, 586 contracted, 572 Simple implementation rows, and zero signed
admissions.

Dead debug/fault/capability aliases are removed from the general I/O façade.
The canonical fault SFFI remains unit-valued, and canonical Vulkan and UPX
owners remain the only capability paths; do not reintroduce boolean success for
configuration setters or shell-based probes in this façade. This deletion-only
slice reduces Simple implementations to 564 rows (522 symbols) without adding
hot-path work. Continue the owner-first queue with remaining constant-success,
empty-on-error, and fabricated capability implementations. Current census is
12,492 declarations, 11,710 untouched, 508 tagged, 586 contracted, and zero
signed admissions.

Signal ownership is consolidated in the library façade: delete the two unused
app copies, remove unconditional capability success, check the actual install
status, reject failed atexit registration, and confine the four raw operations
to explicit `unsafe(ffi)` blocks. The hot path loses a precheck and adds no
lookup, allocation, hashing, or synchronization. Provider execution remains
unverified because the available bootstrap seed rejects `rt_signal_install` as
unknown; do not reinterpret that failure as unavailability or success. Current
census: 12,487 declarations, 11,701 untouched, 512 tagged, 586 contracted, 558
Simple implementation rows, and zero signed admissions. A later memory-focused
slice must bound or reset the callback registry before calling this family
complete.

The signal callback registry is now capped at 33 unique keys and replaces
duplicate signal/atexit callbacks. `COLL008` understands and tests a dominating
capacity-return guard, so the memory proof is tool-enforced rather than
suppressed. Runtime dispatch remains allocation-free and unchanged in
complexity. Compiler/lib/MCP/LSP-MCP source checks pass; do not claim release
verification until the missing native MCP artifact, core SMF/executable smoke
mismatch, bootstrap-seed signal provider gap, and MCP stdio integration failure
are resolved and rerun by their owning lanes.

The first `rt_file` consolidation replaces duplicate `ffi.io` declarations
with an explicit static façade over `sffi.io` and moves crypto fixtures to
semantic byte APIs. Keep the canonical owner as the only place for subsequent
null/status/ownership contracts; do not re-add raw aliases to the compatibility
path. Current census: 12,453 declarations, 11,670 untouched, 510 tagged, 585
contracted, and zero signed admissions. Continue with the remaining direct
`rt_file_*` declarations ranked by production fan-out, preferring semantic
facades over repeated unsafe annotations.

The interpreter file-size and SHA-256 handlers now match native C/Rust failure
sentinels (`-1` and `nil`) instead of fabricating valid-looking zero/empty
values. Keep the single-pass provider behavior. Next lift those raw sentinels
at the canonical Simple owner into `Option`/`Result` without a secondary
last-error query, then migrate callers by semantic need. Six Rust file-provider
tests pass; artifact signing and proof receipts are still absent.

Nullable line and mmap-byte reads are now lifted once at their canonical
owners into `Result`, preserving valid emptiness while rejecting unreadable
paths without a second syscall. Keep this single-pass shape as remaining
nullable arrays/text are migrated. Current census: 12,454 declarations,
11,669 untouched, 513 tagged, 587 contracted, and zero signed admissions.

The backing census now performs one linear Simple-source scan with a hashed
symbol filter rather than recursive multi-pattern grep. Its measured full run
is 34.09 seconds / 75,124 KiB peak RSS; the full safety census is 75.03 seconds
/ 75,560 KiB. Preserve this bounded audit shape while adding contract fields;
never move census, evidence, signature, or symbol-resolution work into the
foreign-call hot path.

Raw `rt_*`/`spl_*` identity now survives module boundaries in both HIR safety
passes: prefix classification requires lexical unsafe authority even when a
callee is absent from the current module's extern table. Keep semantic safe
APIs free of raw prefixes and minimize unsafe to the actual raw call. Focused
gates pass (Rust 4/4, self-hosted 7/7); the broad compiler check repeatedly
printed green batches but did not terminate, which remains tooling evidence to
fix rather than a PASS. This rule changes compile-time analysis only and adds
no foreign-call hot-path work.

The canonical Torch declaration owner is fully tagged (135/135) without adding
per-call wrappers; global tagged rows rise to 645 and untouched rows fall to
11,537, while verified/signed remains zero. Do not call this safe: only one
Torch declaration has even a source-level contract classification. Migrate the
high-level Tensor API to checked nonzero handles and status/out provider shims
before allowing safe exports.

Owned C++ backing discovery now includes `.cc`/`.cpp`/`.cxx`. The new boundary
census/ratchet establishes the starting gate: 211 definitions, 209 missing an
exception barrier, 31 pointer-boundary rows, zero verified/signed. Next split
Torch into versioned C ABI families and translate every C++ exception to typed
status at the shim. Do not add `noexcept` alone where it would merely terminate
on an ordinary operational error, and do not translate exceptions into
fabricated zero/false/empty success values.

CUDA declaration ownership is consolidated: two duplicate `ffi` files are now
static facades and the 34-entry `sffi` owner is fully unsafe-tagged. This
deletes 54 repeated declaration rows and adds no runtime call, branch, lookup,
allocation, or synchronization. Current census: 12,400 declarations, 679
tagged, 587 contracted, 11,449 untouched, zero signed admissions. Next migrate
CUDA handle/status families at this one owner; preserve the C-compatible raw
integer ABI where required while keeping semantic capability APIs boolean.

Engine2d Vulkan now has one raw declaration owner: the dynamic-dispatch module
imports its 24 static symbols from `sffi_vulkan`, whose 57 declarations are all
unsafe-tagged. Current census: 12,376 declarations, 736 tagged, 587 contracted,
11,368 untouched, zero signed admissions. Preserve the direct static-call hot
path. Separately redesign dependency/orphan quarantine admission with bounded
backpressure: current global arrays are unbounded, while a blind cap would
lose ownership and leak GPU resources, and synchronous forced-idle retry would
create a latency regression.

The general Vulkan facade now imports 37 ABI-identical declarations from the
canonical owner and tags its 37 graphics-only raw declarations. Dynamic Torch
now imports 39 ABI-compatible raw symbols from the canonical Torch owner and
keeps 12 unique/legacy declarations explicitly unsafe. Both are compile-time
owner consolidation: no runtime forwarding, lookup, allocation, hashing, or
new branch was added. Current census: 12,300 declaration rows, 785 tagged, 587
contracted, 11,243 untouched, and zero evidence-verified, signature-verified,
or verified-and-signed admissions. Next migrate dynamic Torch's fabricated
zero error paths to typed result/status APIs and versioned provider status/out
shims; do not reinterpret the six fixed-dimension symbols as canonical
descriptor calls, and do not claim an unsafe tag as semantic verification.

Dynamic Torch solve no longer exposes a zero-return compatibility API. Its two
production consumers require the existing explicit result status and positive
handle, and the old source/readiness tests now assert that the fabricated-value
wrapper is absent. Verification: readiness spec 4/4, three focused source
checks pass, lint has zero errors. Continue the same migration family-by-family
for clone/matmul/reductions/creation. Keep one raw call per operation and do not
add hot-path availability rechecks beyond those needed to distinguish provider
absence from a contract violation. The C++ provider still needs a versioned
status/out ABI and signed evidence; this wrapper change alone is not admission.

Clone, matmul, dot, and inverse are the next completed dynamic Torch semantic
family: the zero-handle APIs are removed, typed results reach every production
consumer, and invalid/null handles cannot be lifted as tensors. Readiness tests
pass 5/5; focused checks and lint pass. The hot path keeps one availability
query and one raw operation call, with only input/output contract branches and
no lookup, hashing, I/O, retry, or explicit allocation. Continue with tensor-
returning dimension, activation, scalar, and creation functions, then scalar
reductions whose valid numeric zero must be distinguished from provider error.

Fourteen dynamic Torch scalar/unary tensor operations now preserve failures as
typed results through their shared production dispatchers. Readiness is 7/7;
three focused checks and lint pass. Static call-shape inspection reports one raw
operation call and no explicit allocation per migrated wrapper. Next migrate
the five trigonometric helpers in `dyn_sffi_tensor_ops`, then shape/index and
constructor handle families. Scalar reductions must use a status/value result
because floating-point zero is valid data and cannot remain an error sentinel.

Torch sin/cos/tan/asin/acos/atan2 now use typed results end-to-end and import
their six raw symbols from the canonical owner. Status tests pass 4/4, focused
checks and lint pass, and the ratchet passes. Census is 12,294 rows, 785 tagged,
587 contracted, 11,237 untouched, zero verified/signed; `rt_torch` has 22
untouched rows. Continue with shape/index and constructor/copy families, where
legacy empty-array and zero-handle adapters are still explicitly tested and
must be removed rather than retained as compatibility behavior.

The tensor from-values and copy-values compatibility APIs are now removed.
Every production consumer requires explicit ready/error status before lifting a
handle or accepting copied values; the previous zero/empty fabrication tests
were deleted. Status tests remain 4/4, three focused checks and lint pass. This
shortens the success call path by removing an unwrap wrapper and preserves the
copy routine's existing single buffer allocation/free. Next remove fabricated
handles from reshape/permute/cat/stack/binary/to-float and fixed-dimension
constructors, then address scalar reductions separately.

Contiguous/squeeze/unsqueeze/slice now carry typed results through
`TorchNDArray`; the zero-handle APIs are removed and intermediate slice
ownership is released before error propagation. Readiness passes 8/8, focused
checks and lint pass. Continue with reshape/permute/cat/stack/binary/to-float
inside `dyn_sffi_tensor_ops`, then fixed-dimension constructors and scalar
reductions. Preserve one raw call per logical operation and explicit cleanup
for every intermediate tensor.

Reshape ranks 1-4 and permute ranks 2-4 now return typed results through all
production callers. Status tests pass 5/5, focused checks and lint pass, and
each wrapper keeps exactly one raw operation call. Continue with cat/stack,
binary operations, and to-float; then migrate fixed-dimension constructors and
scalar reductions. Do not combine valid numeric zero with provider failure.

Cat/stack for two through four tensors now preserve typed provider errors
through `TorchNDArray`. Status tests pass 6/6, focused checks and lint pass, and
each wrapper retains one raw call. Next migrate binary operation and to-float,
then fixed-dimension constructors and scalar reductions.

Binary arithmetic and to-float now preserve typed errors through all production
callers. Status tests pass 7/7, focused checks and lint pass, and conversion
ownership is released before result propagation. Continue with fixed-dimension
constructors and dimension reductions, then scalar status/value results.

Dimension sum/mean/min/max/argmin/argmax now preserve typed errors end-to-end.
Readiness passes 9/9, focused checks and lint pass, and index intermediates are
freed before conversion error propagation. Next migrate fixed-dimension
constructors, softmax/leaky-relu, and scalar reductions using status/value
results so legitimate floating-point zero remains distinguishable from error.

Zeros, ones, and full fixed-dimension constructors now preserve typed provider
errors for ranks 1-4. Their production dispatcher no longer repeats the
availability probe, so the successful path remains one availability query and
one direct raw constructor call with constant-time dimension/handle checks.
Readiness passes 10/10 and focused checks pass. Next migrate empty/rand/randn,
then eye/arange/linspace, softmax/leaky-relu, and scalar status/value results.
Signed and evidence-verified admission remains pending; these raw declarations
remain explicitly `unsafe(ffi)`.

Empty, rand, and randn fixed-dimension constructors now preserve typed provider
errors for ranks 1-4 and remove the second availability probe from their owner
dispatcher. Readiness passes 11/11 with the same one-query/one-call hot path.
Next migrate eye/arange/linspace, softmax/leaky-relu, and scalar status/value
results; signed evidence admission remains a separate unfinished phase.

Eye, arange, and linspace now preserve typed errors through `TorchNDArray` and
remove duplicate availability probes. Readiness passes 12/12 while each path
keeps one direct raw constructor call. Next migrate softmax/log-softmax/leaky-
relu, then scalar status/value results; cryptographic provider admission and
C++ exception barriers remain pending.

Softmax, log-softmax, and leaky ReLU now preserve typed errors end-to-end.
Readiness passes 13/13 and each wrapper retains one direct raw call. Next
migrate scalar reductions to status/value results so valid numeric zero cannot
be confused with provider failure; signed admission remains pending.

The census now reports and ratchets `unsafe_minimized_rows` separately from
unminimized unsafe rows, with family/scope evidence and signature columns.
Current totals are 12,294 rows: 327 unsafe-minimized, 11,967 unminimized,
11,237 untouched, and zero verified/signed. Use the largest untouched families
(`rt_file`, `rt_process`, `rt_env`, then `rt_time`) as the next broad migration
order while the cross-lane Torch scalar status/out ABI is designed.

Twelve migrated Torch raw handle declarations now state their enforced
nonpositive-handle sentinel, raising contract-documented rows to 599 and
unsafe-minimized rows to 327. Do not apply this annotation to scalar reductions
until their status/value ABI removes the valid-zero ambiguity.

The restarted dedicated-worktree audit completed the remaining Torch
declaration slice. Canonical imports replace seven duplicate or missing raw
declarations, fixed tensor operations are explicitly unsafe-tagged, and the
copy lift validates expected count, multiplication bounds, and exact provider
copy count before reading. Focused status coverage passes 7/7. Census is now
12,287 rows, 800 tagged, 614 contracted, 342 unsafe-minimized, 11,215 untouched,
and zero verified/signed. Next implement compiler-owned typed status/out thunks
for the eight scalar reductions across interpreter, JIT, native, and C++;
retain a stack output, one provider call, and no hot-path lookup or allocation.
After that, migrate the five piped-process declarations in
`src/lib/editor/services/debug_session_dap.spl` without claiming its empty-read
sentinel is fully safe.

The eight Torch scalar reductions now have collision-free status/out C++
entrypoints and typed dynamic Simple results. C++ catches exceptions and writes
the output only on success; native callers use a stack slot, and interpreter
callers cache typed function pointers once. `torch-scalar-status-out-contract`
ratchets the one-call/no-allocation/no-lookup shape. Readiness passes 15/15 and
the census is 12,295 rows, 808 tagged, 622 contracted, 350 unsafe-minimized,
11,215 untouched, and zero verified/signed. Do not remove the unsafe label yet:
legacy bare scalar exports, static Torch trait consumers, provider signing, and
evidence admission remain open. Next migrate the static scalar consumers or
change their interfaces to typed results, then take the bounded piped-process
family and implement signed provider admission separately.

The static Torch scalar migration is now complete for repository-owned live
callers. Backend trait methods, three ownership-family implementations,
gradient clipping, accuracy, `Tensor.sum`, and the CUDA optimizer probe all
propagate checked `Result<f64, text>` values. Bare scalar ABI declarations are
retained only as internal, explicitly unsafe compatibility declarations and
are no longer facade exports. Cleanup happens before error propagation. The
focused source checks, 15/15 readiness cases, and the source-shape contract
gate pass. The gate deliberately claims only one checked ABI call, cached
interpreter lookup after initialization, and no explicit wrapper allocation;
it does not claim libtorch reductions are allocation-free or synchronization-
free. Next harden the bounded piped-process family, then implement real signed
evidence admission. Current global admission remains zero, so neither all
Torch SFFI nor all SFFI may be described as verified safe.

The bounded editor DAP process slice now consumes the canonical process owner
instead of declaring five additional raw externs. Typed spawn/write/close
helpers prevent failed writes from becoming sent/pending requests and prevent
failed cleanup from becoming a stopped state. Piped cleanup replaces generic
PID kill. The success path preserves one liveness query plus one write and adds
no map, lookup, hashing, retry, sleep, or explicit allocation. Nine system
examples, focused check/lint, and `editor-dap-process-sffi-contract.shs` pass.
The gate intentionally labels stdout `unsafe_ambiguous`: implement an additive
status-bearing nonblocking read/liveness ABI across C, Rust interpreter, JIT,
native, and Simple wrappers before promoting this family beyond unsafe-
minimized. After that, migrate `lsp_transport.spl` and editor smoke/runtime
duplicates to the same owner, then return to signed provider admission.

The checked read/liveness ABI is now implemented across those source lanes and
keeps a bounded one-observation poll path. Native behavioral coverage and both
static source-shape gates pass. Do not promote it beyond `unsafe_unsigned` yet:
the compiled interpreter artifact is stale, returned C buffers and slot access
still need an explicit serialization/thread policy, and no provider evidence
manifest has been signed or admitted. Next actions are:

1. rebuild the compiler and rerun checked status behavior in the compiled
   interpreter;
2. add and verify owning serialization plus close-after-EOF lifecycle;
3. migrate LSP/editor duplicate read/liveness consumers to the checked owner;
4. bind runtime artifact, compiler, ABI registry, and verification receipt to a
   real signature and loader admission;
5. continue `rt_file`, remaining `rt_process`, `rt_env`, and `rt_time` without
   weakening the one-call/no-unbounded-allocation gates.

Current census: 12,295 rows, 810 tagged, 626 contracted, 352 minimized, 11,211
untouched, and zero evidence-verified, signature-verified, or admitted.

Evidence admission v2 now derives admission from a parsed ABI closure, exact
function-only closure in a target-matched Linux ELF provider, immutable input
snapshots, exact source/build/compiler/ABI identities, actual canonical receipt
files rather than asserted hashes, detached
Ed25519 signature, and separately provisioned provider trust. The first bounded
production target is the three scalar clock contracts. Its live production gate
must remain BLOCKED without externally supplied evidence and trust; the
integration key is fixture-only. Next bind the real Stage4-selected runtime
archive and release signing authority, bind the final consumer artifact, link
map, linker, target, and ABI in its native-link receipt, then run the census
with those evidence inputs. A fixture admission remains `fixture_verified`,
never production `verified_and_signed`. Do not promote the remaining
273 matching clock declaration rows unless each duplicate is also lexically
unsafe-tagged and contract-documented. No admission operation belongs on the
clock call path.

Piped-process concurrency proceeds without weakening the bounded hot path.
First use one fixed thread-local native checked-read buffer and stable fixed
Rust slots with atomic PID tags and per-child locks, so unrelated children do
not serialize behind a registry and native results
are not shared across threads. This adds no per-call native allocation and
keeps the 8 KiB read bound. Do not move the 64 KiB DAP accumulator to TLS:
move it into its process/session owner. Next add generation-bearing opaque handles with
direct slot lookup and explicit
`RESERVED/ACTIVE/CLOSING/FREE` states, and caller-buffer checked reads. Keep
raw PID/text-return compatibility entry points tagged unsafe until consumers
migrate; TLS/per-child locking alone is not verification of the family.

Performance checkpoint: the first `Mutex<HashMap<PID, Arc<Mutex<Child>>>>`
prototype regressed an isolated lookup/lock model from 23.56 to 51.43 ns/op at
one thread and from 91.40 to 165.94 ns/op at four threads (2,048 KiB peak RSS
for all runs). The final fixed-slot shape measures 24.66 ns/op at one thread
and 40.58 ns/op at four threads in the lock-only stress model, versus 23.56 and
91.40 ns/op. More representative nonblocking-read measurements are 685.76 ->
717.39 ns/op at one thread (+4.6%) and 995.75 -> 263.57 ns/op across four
independent children (-73.5%), at the same observed 2,048 KiB RSS floor.
Lookup is bounded to 16 contiguous atomic tags, adds no allocation/copy or
reference counting, and holds only the selected child mutex across I/O.
The exact native fixture comparison
was 2.02 s/2,048 KiB before and 1.96 s/2,048 KiB after, but both exited status 6
in this environment, so it is performance evidence only and a correctness
blocker remains recorded rather than retried.

The incremental-cache owner now has lexical authority for its file, directory,
environment, CLI, PID, and time calls. Preserve branch-local failure identity,
one traversal, and one digest per artifact. Its content fingerprint now requests
SHA-256 rather than a collision-prone integer hash. Next harden the canonical
`sha256_text`/text-byte conversion boundary itself: explicitly contract and
scope its two runtime calls, retain one conversion plus one cached/direct digest
call, keep the pure-Simple fallback, and do not call that provider verified until
signed evidence is admitted. The summary-only call-authority census is the
required low-output ratchet command; current counts are 21,331 raw, 1,970
explicit, and 19,361 missing.

The canonical SHA-256 text boundary is now unsafe-minimized: duplicated text-
byte declarations are removed, string-core owns the raw conversion, and the
accelerator retains one checked call plus pure-Simple fallback. Keep its fixed
64-slot hex buffer; do not reintroduce growing-string concatenation. Current
authoritative totals are 12,053 unsafe declaration rows, 365 minimized, 10,954
untouched, and zero signed/admitted. Next prioritize `rt_file` (2,604 untouched),
`rt_process` (970), `rt_env` (459), and `rt_time` (354), while preserving the
one-call/no-lookup/no-unbounded-allocation rule. The repaired census must keep
file-output mode and must never read `/dev/stdout` as an input.

`driver_public_shared.spl` is now call-authority complete without changing its
ordered file-probe or process-call cardinality. Keep its 27 direct lexical calls
and failure-sentinel initialization; do not replace the constant ordered binary
probes with an allocated candidate table on this startup path. The next bounded
`rt_file` owners are compiler cache stamp/lease/GC modules; prefer owners whose
nullable reads and write/delete statuses can be preserved without fabricating
empty data or adding a second provider call.

The file-stamp cache owner is now call-authority complete with its exact torn-
read observation sequence and retry bound retained. Next take `cache/lease`:
preserve one directory listing per sweep, one liveness query per parsed lease,
and one write/delete per state transition. Do not turn its empty read, false
write/delete, negative clock/PID, or empty listing sentinels into success.

The lease owner and fast-GC owner are now unsafe-minimized at their raw call
sites. Fast GC must retain confirmed-mutation accounting and reject negative
mtime/PID/clock sentinels. Its hot path remains O(n²) oldest-first selection,
one mtime observation per remaining candidate, and the existing collection
shape; do not add retries, generic dispatch, or per-item wrapper allocation.
Current inventory is 21,382 calls (2,066 explicit, 19,316 missing) and 12,077
declaration rows (867 tagged, 377 minimized, 10,945 untouched, zero signed or
admitted). Next harden `cache/gc/mark_sweep.spl`, then `admission.spl`, using
the same confirmed move/delete rule. Self-hosted verification remains pending
because the available executable reports that it is the Rust bootstrap seed.

Mark-sweep now preserves its one-read/one-walk call bounds and reports only
confirmed moves. Current totals are 21,382 calls (2,079 explicit, 19,303
missing) and 12,077 declarations (875 tagged, 380 minimized, 10,937 untouched,
zero signed/admitted). Next harden `cache/gc/admission.spl`: keep its single
tree traversal and size probes, and do not interpret absent/inaccessible/provider
failure as proof that capacity is available.
