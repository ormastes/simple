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

### Completed header shared-library flags authority slice

- [x] Remove the module-local raw environment declaration and call.
- [x] Retain the local nullable API through canonical always-inline
  `env_get_opt`.
- [x] Preserve both conditional MinGW environment lookups and all platform
  process-probe behavior.
- [x] Add a static authority and call-count ratchet.

### Completed duplicate-check scalar math authority slice

- [x] Tag the raw square-root declaration explicitly `unsafe(ffi)`.
- [x] Confine all calls to the existing always-inline scalar owner.
- [x] Preserve one O(n) accumulation and exactly two roots per dense cosine.
- [x] Add no hot-path work and add a static call-count ratchet.
- [x] Remove the feature-vector builder's raw-symbol import and call.
- [x] Preserve one root after its single O(n) weight accumulation.

### Completed MDSOC layer-document read authority slice

- [x] Remove the checker-local non-null raw file-read declaration and calls.
- [x] Route all four reads through typed `file_read_result`.
- [x] Return conservative query failure on `Err` without fabricating empty text.
- [x] Preserve valid empty files, read counts, and search complexity.
- [x] Keep the bounded typed-result lift outside line-scan loops.
- [x] Add a static typed-read and fail-closed ratchet.

### Completed MDSOC module-storage contract slice

- [x] Replace the untyped source callback with a typed `Result` function.
- [x] Remove raw disk-read authority and delegate once to `file_read_result`.
- [x] Preserve registered empty memory sources as `Ok("")` and return `Err` for
  absence.
- [x] Add no read or registry-scan work and add a static contract ratchet.

### Completed duplicate-check incremental-write authority slice

- [x] Remove the module-local raw file-write declaration and call.
- [x] Delegate to canonical one-call `file_write_exact` after the existing
  parent-directory setup and serialization.
- [x] Preserve boolean failure reporting without retry or metadata probes.
- [x] Add a static authority and one-write-shape ratchet.

### Completed duplicate-check detector-path authority slice

- [x] Correct raw path canonicalization from non-null text to `text?`.
- [x] Tag and confine the single provider call to an always-inline owner.
- [x] Reject null/empty canonicalization before directory walking.
- [x] Preserve one path call, one walk, and existing filtering on success.
- [x] Add a static nullable-contract and call-count ratchet.

### Completed tiered-JIT authority slice

- [x] Remove the unused raw `rt_jit_call_i64_i64` declaration.
- [x] Tag the remaining seven raw JIT/clock declarations `unsafe(ffi)`.
- [x] Confine each primitive to one always-inline lexical owner.
- [x] Preserve lazy creation, two compile clock reads, and direct native calls.
- [x] Distinguish null compile transport from empty-text success and report
  `E-SFFI-017` on the cold promotion path.
- [x] Keep provider admission off hot paths and add a static call-count ratchet.

### Completed MIR interpreter async-runtime authority slice

- [x] Tag actor spawn/send/receive and scheduler yield `unsafe(ffi)`.
- [x] Confine each primitive to one always-inline lexical owner.
- [x] Preserve runtime-name dispatch, timeout behavior, and provider calls.
- [x] Record the legacy malformed-argument zero as an open `Result` migration.
- [x] Add no scheduler hot-path work and add a static call-count ratchet.

### Completed MIR interpreter core authority slice

- [x] Remove raw environment declaration/calls and retain two startup reads via
  canonical nullable `env_get_opt`.
- [x] Tag and confine enum discriminant to one always-inline lexical owner.
- [x] Keep all three discriminant calls on unknown-value error paths only.
- [x] Add no normal dispatch work and add a static call-count ratchet.

### Completed compiler performance CLI authority slice

- [x] Remove both duplicate raw `rt_get_args` declarations and calls.
- [x] Route both entrypoints through the canonical explicitly unsafe CLI owner.
- [x] Preserve one argument-array fetch per process entrypoint.
- [x] Keep benchmark and optimizer loops unchanged and add a static ratchet.

### Completed SSA and AOP environment-authority slice

- [x] Remove both module-local raw environment declarations and calls.
- [x] Route SSA debug and AOP configuration reads through canonical nullable
  `env_get_opt`.
- [x] Preserve two mutation-visible SSA debug checks and four AOP reads.
- [x] Add no cache or hot-path work and add a static call-count ratchet.

### Completed MIR optimizer environment-authority slice

- [x] Remove the module-local raw environment declaration and call.
- [x] Retain the shared nullable helper through canonical always-inline
  `env_get_opt`.
- [x] Preserve mutation-visible trace/bootstrap reads and the one-read
  verify-each cache.
- [x] Add a static authority, call-count, and cache-shape ratchet.

### Completed C-import header-read authority slice

- [x] Remove the raw non-null C-header file-read declaration.
- [x] Make the private header reader return typed `Result<text,text>`.
- [x] Route provider failure to the existing explicit import error.
- [x] Preserve exactly one read and existing empty-header behavior.
- [x] Add no retry, scan, allocation, cache, hash, lock, or dispatch.
- [x] Add a static typed-contract and call-count ratchet.

### Completed lazy module-loader authority slice

- [x] Remove raw file-read and environment declarations.
- [x] Make candidate file transport typed `Result<text,text>`.
- [x] Preserve unreadable/empty-source eager fallback behavior.
- [x] Cache `SIMPLE_LIB` once between existing lazy-loader resets.
- [x] Preserve at most one file read per requested candidate and one scan.
- [x] Add no extra search, scan, allocation, hash, lock, or dispatch.
- [x] Add a static typed-contract, call-count, and cache-shape ratchet.

### Completed interpreter CLI argument-authority slice

- [x] Remove the duplicate raw `rt_cli_get_args` declaration.
- [x] Route the sole fetch through canonical `std.io_runtime.get_args`.
- [x] Preserve `[text]` semantics and one argument fetch per parse.
- [x] Preserve the existing program/script-prefix skip and argv pass.
- [x] Add no numeric workaround, second scan, cache, lock, or dispatch.
- [x] Add a static authority and one-fetch ratchet.

### Completed interpreter JIT state-authority slice

- [x] Remove four raw file and PID declarations.
- [x] Use typed reads, exact writes, canonical delete, and validated PID.
- [x] Preserve one provider operation for every existing load/save/cleanup.
- [x] Add no retry, metadata probe, allocation, cache, lock, or dispatch.
- [x] Record repeated file I/O on `jit_record_call` as open measured-design debt.
- [x] Add a static authority and operation-shape ratchet.

### Completed core interpreter module-loader authority slice

- [x] Remove raw environment/file declarations and unused path-join authority.
- [x] Make the private module-source contract `Result<text,text>`.
- [x] Preserve one read, empty rejection, depth restoration, and parse per entry.
- [x] Cache GC-warning tracing once between existing loader resets.
- [x] Add no path normalization, search, scan, allocation, lock, or dispatch.
- [x] Add a static typed-contract, call-count, and cache-reset ratchet.

### Completed interpreter declaration-profile authority slice

- [x] Remove the duplicate raw non-null environment declaration.
- [x] Seed the assurance profile through canonical nullable `env_get_opt`.
- [x] Preserve one initialization read and later explicit policy reapplication.
- [x] Preserve default behavior for unset, empty, or failed provider input.
- [x] Add no loop work, allocation, cache, hash, lock, or dispatch.
- [x] Add a static one-read authority ratchet.

### Completed MIR bulk-ops flag spec authority slice

- [x] Remove the spec-local raw environment setter declaration and calls.
- [x] Route all three setup mutations through canonical `env_set`.
- [x] Assert every boolean setter status before checking optimizer behavior.
- [x] Keep compiler-runtime and optimizer hot paths unchanged.

### Completed compiler performance-clock authority slice

- [x] Tag profiler, trace, and benchmark monotonic clocks `unsafe(ffi)`.
- [x] Confine each clock to a file-local always-inline lexical owner.
- [x] Tag and confine non-status-bearing benchmark timestamp text.
- [x] Preserve one direct provider call per sample and add no timing-path work.
- [x] Add a static authority and call-count ratchet.

### Completed builtin type-registry authority slice

- [x] Tag nullable lookup and boolean membership declarations `unsafe(ffi)`.
- [x] Confine both primitives to always-inline lexical owners.
- [x] Preserve nullable and boolean APIs without zero/empty substitution.
- [x] Preserve exactly one direct provider call per query.
- [x] Add no hot-path admission, hash, lookup, allocation, lock, or dispatch.
- [x] Record absence/provider-failure ambiguity as unverified and unsigned.

### Completed SIMD capability authority slice

- [x] Tag ten host/device capability primitives `unsafe(ffi)`.
- [x] Confine every primitive to an always-inline direct lexical owner.
- [x] Preserve architecture, CPUID, HWCAP, sysctl, RISC-V, and CUDA call counts.
- [x] Remove two raw file-read declarations and use one typed read per path.
- [x] Preserve empty/zero scalar fallback without fabricating successful data.
- [x] Add no vector-loop work, admission, hashing, cache, lock, or dispatch.
- [x] Record sentinel-bearing providers as unsafe, unsigned, and unverified.

### Completed MIR statement-lowering authority slice

- [x] Remove unused raw dictionary and duplicate environment declarations.
- [x] Route both debug reads through canonical nullable `env_get_opt`.
- [x] Tag and confine discriminant and payload projections `unsafe(ffi)`.
- [x] Correct the expression payload contract to nullable and reject nil.
- [x] Preserve projection counts and statement-dispatch complexity.
- [x] Add no admission, hashing, allocation, cache, lock, or extra dispatch.
- [x] Record the tagged runtime provider as unsafe, unsigned, and unverified.

### Completed MIR function/type-lowering authority slice

- [x] Tag the sole tagged-value discriminant declaration `unsafe(ffi)`.
- [x] Confine all 22 projections to one always-inline lexical owner.
- [x] Preserve GPU/type dispatch projection and branch counts.
- [x] Add no admission, hashing, allocation, cache, lock, or extra dispatch.
- [x] Record the discriminant provider as unsafe, unsigned, and unverified.

### Completed MIR bootstrap process-authority slice

- [x] Remove duplicate raw exit declarations from both bootstrap modules.
- [x] Route all twelve fatal sites through the canonical exit owner.
- [x] Remove the raw string-length declaration and unused split-based helper.
- [x] Preserve one exit call per fatal site and add no normal-path work.
- [x] Add a static authority and fatal-call-count ratchet.
- [x] Record the centralized runtime provider as unsigned and unverified.

### Completed MIR module-lowering environment-authority slice

- [x] Remove the duplicate raw nullable environment declaration.
- [x] Retain one always-inline helper through canonical `env_get_opt`.
- [x] Preserve four reads and disabled fallback for unset/empty values.
- [x] Add no loop work, cache, allocation, hash, lock, or extra dispatch.
- [x] Add a static authority and call-count ratchet.
- [x] Record the canonical provider as raw, unsigned, and unverified.

### Completed admission identity-join hardening slice

- [x] Preserve admitted symbol, source-signature, and provider identities.
- [x] Reject admitted symbol/signature pairs absent from owned declarations.
- [x] Join `reverified` on symbol plus canonical ABI signature, never name alone.
- [x] Keep source evidence claims non-authoritative and fail closed on mismatch.
- [x] Add a static regression assertion for the composite join key.
- [x] Add zero compiler, loader, admission-hot-path, or per-call runtime work.

### Completed frontend parse-cache authority slice

- [x] Remove all nine cache-local raw SFFI declarations.
- [x] Preserve four env reads, two existence probes, and one typed file read.
- [x] Preserve one non-shell hash, exact write, move, and failure cleanup.
- [x] Fail closed on invalid PID and keep provider failures as cache misses.
- [x] Avoid duplicate digest validation, extra retry, scan, lock, or dispatch.
- [x] Add a static authority and exact operation-count ratchet.

### Completed frontend trace environment-authority slice

- [x] Remove the frontend runner's duplicate raw environment declaration.
- [x] Use one always-inline process-lifetime tri-state trace gate.
- [x] Reduce two provider reads per module to at most one per process.
- [x] Preserve boolean/default-off trace behavior and both receipts.
- [x] Add no parse-loop scan, allocation, hash, lock, or dynamic dispatch.
- [x] Add a static authority, call-count, and cache-shape ratchet.

### Completed driver action-index authority slice

- [x] Remove all eight action-index-local raw SFFI declarations.
- [x] Preserve one existence probe and one typed read per lookup.
- [x] Preserve two directory creates and one exact atomic publication attempt.
- [x] Preserve failed-move cleanup and the existing lost-race re-read.
- [x] Fail closed on invalid PID/clock without fabricated temp-file identity.
- [x] Add no retry, scan, allocation, hash, lock, or dynamic dispatch.
- [x] Add a static authority and exact operation-count ratchet.

### Completed MIR switch/operator environment-authority slice

- [x] Remove the duplicate raw nullable environment declaration.
- [x] Retain the always-inline helper through canonical `env_get_opt`.
- [x] Preserve all five environment and 16 discriminant query sites.
- [x] Update the existing cross-lane audit rather than add a duplicate tool.
- [x] Add no call, branch, allocation, cache, hash, lock, or dispatch.
- [x] Record the remaining discriminant provider as unsafe and unverified.

### Completed MIR expression-dispatch environment-authority slice

- [x] Remove the duplicate raw nullable environment declaration.
- [x] Collapse two environment wrappers into one always-inline canonical owner.
- [x] Preserve all six environment and 115 tagged projection query sites.
- [x] Update the existing cross-lane audit and exact call-count ratchets.
- [x] Remove one potential call layer and add no branch/allocation/dispatch.
- [x] Record tagged projection providers as unsafe and unverified.

### Completed MIR literal-lowering dead-authority slice

- [x] Remove unused raw dictionary, environment, and discriminant declarations.
- [x] Introduce no replacement wrapper or duplicate authority.
- [x] Preserve generated MIR, loops, dispatch, calls, and allocations exactly.
- [x] Add a static no-raw-authority ratchet.

### Completed MIR method-lowering authority and trace-cost slice

- [x] Remove dead raw dictionary and duplicate environment declarations.
- [x] Tag and confine both live discriminant projections `unsafe(ffi)`.
- [x] Replace eight repeated debug reads with two one-read tri-state gates.
- [x] Preserve default-off boolean behavior without integer API substitution.
- [x] Reduce provider calls and add no allocation, hash, lock, or dispatch.
- [x] Add a static authority, call-count, and cache-shape ratchet.
- [x] Record both providers as unsafe, unsigned, and unverified.

### Completed MIR data environment-authority slice

- [x] Remove the duplicate raw non-null environment declaration.
- [x] Remove five module-local unsafe blocks through canonical `env_get_opt`.
- [x] Preserve all eight reads and the existing outer-scope trace cache.
- [x] Preserve disabled behavior for unset and explicitly empty values.
- [x] Add no loop work, allocation, hash, lock, cache, or dispatch.
- [x] Add a static authority and call-count ratchet.
- [x] Record the canonical provider as raw, unsigned, and unverified.
## 2026-08-26 module-resolution environment authority follow-up

- Removed the duplicate module-resolver `rt_env_get` declaration and wrapper.
- Kept path join/dirname as direct always-inline owners with unchanged probe
  ordering and counts.
- Deferred any `SIMPLE_LIB` value cache because it would change visibility of
  environment mutation; canonical ownership alone adds no intended hot-path
  allocation, lookup, or copy.
- Status: source-reviewed, deliberately unverified for this sync.
## 2026-08-26 lexer nullable-environment authority follow-up

- Added canonical `env_get_nullable` for exact optional transport semantics.
- Removed the lexer's duplicate raw environment declaration and unsafe wrapper.
- Preserved thirteen read call sites, empty-versus-nil behavior, and the
  one-direct-call hot-path shape; added no allocation, copy, lookup, or retry.
- Kept the remaining three lexer ABIs locally unsafe pending their own typed
  ownership migrations.
- Status: source-reviewed, deliberately unverified for this sync.
## 2026-08-26 lexer nullable-file authority follow-up

- Added canonical `file_read_nullable` for exact one-call optional transport.
- Removed the lexer's duplicate raw file-read declaration and unsafe wrapper.
- Preserved two read call sites, nil/empty behavior, and direct-call hot-path
  shape with no Result allocation, conversion, lookup, normalization, or retry.
- Retained and documented the layer-0 driver source raw owner as unsafe because
  facade import would violate compiler layering.
- Status: source-reviewed, deliberately unverified for this sync.
## 2026-08-26 lexer environment-write authority follow-up

- Made canonical `env_set` always-inline and removed the lexer duplicate.
- Preserved twenty-eight write sites, boolean status ABI, and ignored-result
  behavior with one direct call and no allocation, copy, lookup, lock, or retry.
- Reduced lexer raw declarations to the locally owned array-release boundary.
- Status: source-reviewed, deliberately unverified for this sync.
## 2026-08-26 lexer array-release provider follow-up

- Kept `rt_array_free(i64)` explicitly unsafe; the type cannot prove ownership.
- Changed the Rust interpreter provider from wrong-type silent success to its
  existing typed integer-conversion error path.
- Added a static cross-provider ratchet for Rust type rejection and C/Simple
  invalid/unregistered-handle guards.
- Preserved the valid path's existing type match and one release dispatch; no
  allocation, copy, hash, lookup, lock, retry, or extra traversal was added.
- Status: source-reviewed, deliberately unverified and unsigned.

## 2026-08-26 CUDA I/O owner checkpoint

- Tag and contract all 25 raw CUDA declarations at the canonical I/O owner.
- Reconcile pointer-write returns with the exact unit-returning C/Rust ABI.
- Close native/interpreter identity coverage for device-to-device copy,
  extended launch, and error text using compiler-owned typed registrations.
- Reuse the existing extended-launch interpreter implementation rather than
  adding a duplicate dispatch path.
- Remove redundant feature-path name allocation and the per-call CUDA error
  text allocation/leak; retain direct typed calls and existing validation.
- Cache successful device names once per actual device handle; use static text
  for invalid devices, preserve process-lifetime pointer validity, and bound
  retained allocations by discovered devices rather than call count.
- Add a source-only owner ratchet that checks exact writes, both-lane identity,
  and static error text without claiming signature admission.
- Remaining production debt: 4,470 unsafe-tag gaps, 6,224 contract gaps, and
  zero signed-admitted declarations.

## 2026-08-26 simple-core string/Any checkpoint

- Reconcile `rt_value_float` with the exact C/Rust/native `[F64] -> [I64]`
  contract and remove the raw-bit integer workaround.
- Tag and contract 35 bootstrap string declarations and four dynamic-Any
  declarations without changing their direct call algorithms.
- Ratchet exact provider signatures so future register-class drift fails a
  source audit.
- First minimization slice complete: all four dynamic-Any operations and the
  string parser's float constructor use private mandatory-inline lexical
  unsafe thunks, with no direct raw calls in their semantic bodies.
- Bootstrap string minimization complete: all 35 raw identities have one
  mandatory-inline lexical unsafe thunk and no additional executable raw call;
  pointer capabilities are confined to the thunks that carry raw pointers.
- Complete the remaining `core_values` and `core_enum` owners: 13 existing raw
  declarations plus the exact `spl_f64_to_bits(f64)` provider dependency are
  tagged and confined, leaving zero untagged `simple_core` externs.
- Align the Simple `rt_value_float` provider itself to `f64`; callers and all
  provider lanes now agree on the floating register class.
- Remaining production debt after this pass: 4,418 unsafe-tag gaps, 6,172
  contract gaps, and zero signed-admitted declarations.
- Remaining production debt: 4,431 unsafe-tag gaps, 6,185 contract gaps, zero
  signed-admitted declarations.

## 2026-08-26 package owner checkpoint

- Consolidate three package declaration owners into one canonical 11-contract
  owner, one bootstrap mirror, and declaration-free compatibility facades.
- Retire 38 unused duplicate declarations, all broken Cargo wrappers, and the
  obsolete `rt_package_free_string` provider/symbol.
- Preserve hash failure as `text?` and existence/directory provider failure as
  `bool?`; do not manufacture empty text or false.
- Confine each retained raw identity to one mandatory-inline thunk and require
  both native/interpreter registry identities.
- Remaining production debt: 4,356 unsafe-tag gaps, 6,110 contract gaps, zero
  signed-admitted declarations.

## 2026-08-26 repository-wide inventory checkpoint

- Production source currently contains 7,259 declarations / 3,815 symbols;
  4,495 declarations lack an FFI unsafe tag and, after the Cranelift update,
  6,249 lack a recognized
  return/error contract.
- The `rt_*` production subset contains 5,806 declarations / 3,051 symbols;
  3,332 lack an unsafe tag, 5,060 lack a contract, and zero are signed-admitted
  without configured exact-artifact admission jobs.
- First close owners that are already centralized and fully unsafe-tagged;
  their contract metadata can be corrected without widening runtime hot paths.
- Cranelift checkpoint: classify all 78 declarations as unsafe with explicit
  empty-string or zero/false/ignored-operation semantics; retain the current
  direct wrapper shape and add no runtime work.
- Next prioritize live production declarations lacking unsafe authority,
  grouped by owner/provider rather than mechanically tagging test fixtures or
  unrelated language-level extern declarations.
- Status: source-censused; no build, runtime, signature, or semantic
  verification claim.

## 2026-08-26 public RuntimeValue closure completion

- Remove the unused public equality and print RuntimeValue wrappers rather
  than adding interpreter dispatch solely to make asymmetric inventory appear
  complete.
- Keep native-backend lowering private to its existing backend owner.
- Ratchet the canonical runtime owner to 11 both-lane contracts and the
  compiler minimal facade to 20 both-lane contracts, with zero asymmetric or
  providerless declarations in either scoped owner.
- Preserve the hot path: this is deletion-only for runtime behavior and adds
  no allocation, copy, lookup, hashing, branch, or dispatch.
- Continue to classify retained SFFI as unsafe and unsigned until semantic
  evidence and exact-artifact signature admission are operational.
- Status: source-reviewed, deliberately unverified and unsigned.

## 2026-08-26 providerless no-GC API removal

- Remove `rt_gc_init`, `rt_gc_malloc`, and `rt_gc_collect` from the no-GC and
  compiler-minimal owners because the reference-count runtime has no provider.
- Reject the pure-runtime zero-return placeholder as a replacement; it has no
  shared allocator state and cannot establish collection.
- Remove three MCP periodic hooks and their now-dead counters. This eliminates
  one increment, modulo, and branch per request plus a delayed unresolved call
  every 100 requests.
- Reach zero providerless declarations in both scoped owners: canonical 11
  both/3 one-lane; compiler-minimal 20 both/3 native-only.
- Measure long-session MCP RSS/allocation behavior only when verification is
  authorized, then fix the actual reference-count owner if retention remains;
  never restore a no-op GC hook.
- Continue closing the three one-lane/native-only functions and require signed
  exact-artifact admission before any safe promotion.
- Status: source-reviewed, deliberately unverified and unsigned.

## 2026-08-26 providerless pointer-era value API retirement

- Remove active raw string/type/free/arithmetic/less-than declarations and
  wrappers after confirming there is no C, Rust, or interpreter provider and
  no production consumer.
- Remove their public interning specs while retaining internal full-generator
  provider fixtures until that generator is separately redesigned.
- Rewrite the obsolete minimal-FFI sample to cover only both-lane tagged scalar
  constructors, predicates, and projections; preserve semantic booleans.
- Reduce canonical closure to 11 both, 3 one-lane, 3 providerless and
  compiler-minimal closure to 20 both, 3 native-only, 0 interpreter-only, 3
  providerless.
- Add no live allocation, copy, branch, lookup, hash, dispatch, or layout work.
- Resolve the remaining GC trio by replacing live `gc_collect` users with the
  actual memory-owner policy or by implementing one verified owner; never add
  a no-op success fallback.
- Status: source-reviewed, deliberately unverified and unsigned.

## 2026-08-26 dead RuntimeValue inspection/clone removal

- Remove unused string/array/dictionary predicates, raw string projection, and
  raw clone from active owners, facades/exports, and both generator mirrors.
- Preserve the live string-constructor generation test with nonnull creation
  and release coverage only.
- Reduce canonical RuntimeValue closure to 11 both, 3 one-lane, and 11
  providerless; reduce compiler-minimal closure to 20 both, 3 native-only, 0
  interpreter-only, and 11 providerless.
- Add no runtime operation, allocation, copy, lookup, branch, hash, dispatch,
  or layout change because the removed APIs had no consumer.
- Next classify the providerless arithmetic/string/GC remainder against its
  real consumers; do not delete the live arithmetic and string paths.
- Status: source-reviewed, deliberately unverified and unsigned.

## 2026-08-26 dead RuntimeValue container-constructor removal

- Remove `rt_value_array_new` and `rt_value_dict_new` from both active owners,
  facades/re-exports, and mirrored SFFI generator specifications after proving
  that no consumer exists.
- Prefer deletion over implementing providers for unused copyable raw handles.
- Reduce canonical RuntimeValue closure to 11 both, 3 one-lane, and 16
  providerless; reduce compiler-minimal closure to 20 both, 3 native-only, 0
  interpreter-only, and 16 providerless.
- Preserve performance and memory behavior: there was no callsite, and no new
  call, allocation, copy, lookup, branch, hash, dispatch, or layout is added.
- Continue classifying the remaining 16 providerless declarations by actual
  consumers before deciding whether to remove or implement them.
- Status: source-reviewed, deliberately unverified and unsigned.

## 2026-08-26 file-delete ABI reconciliation

- Remove the unused raw `file_delete_ptr` compiler-minimal declaration and
  re-export instead of retaining a second conflicting signature.
- Standardize live C and Rust `rt_file_delete` providers on `(pointer, length)`
  and publish the exact `[I64, I64] -> [I8]` native contract.
- Tag and lexically confine the self-hosted interpreter's live raw call.
- Reuse the bounded stack path converter in both C providers; make
  `rt_file_remove` delegate directly, eliminating its per-call heap allocation
  and redundant copy.
- Minimal-facade closure is now 20 both lanes, 3 native-only, 0
  interpreter-only, and 18 neither. Next classify/remove the 18 providerless
  declarations before implementing any new provider.
- Keep deletion unsafe and unsigned until exact-artifact admission and
  cross-lane sabotage evidence exist.
- Status: source-reviewed, deliberately unverified and unsigned.

## 2026-08-26 provider-language census correction

- Report every observed implementation language per extern symbol instead of
  selecting only the first backing class in priority order.
- Distinguish C, C++, header-owned C/C++, Rust exports, Rust interpreter
  handlers, system C, external C ABI, freestanding, and unknown linked-native
  provenance while preserving the existing backing/admission schema.
- Keep implementation presence separate from safe or signed admission; only a
  freshly reverified provider/signature/ABI identity may populate the admitted
  count.
- Add no production runtime work; the change is confined to offline census
  scripts and their fixture.
- Next regenerate the global ledger only under an authorized verification pass,
  then prioritize multi-language signature variants and untouched live calls.
- Status: source-reviewed, deliberately unverified and unsigned.

## 2026-08-26 provider-scoped census admission follow-up

- Added declaration provider identity to the SFFI inventory schema.
- Bound cryptographic admission to symbol + canonical source signature hash +
  provider ID; missing/mismatched provider metadata fails closed.
- Added provider-declared, provider-missing, and multi-provider-symbol census
  metrics so provider attribution debt cannot disappear inside generic unsafe.
- Made symbol-level admission total: every declaration must be admitted before
  the symbol is counted as fully admitted; mixed coverage stays migration debt.
- Preserved module-scoped textual callsite counts as an explicitly named
  distinct-symbol estimate for prioritization, never as resolved-call or lexical
  unsafe-minimization proof.
- Renamed annotation-derived “minimized” counts to contract-declared unsafe and
  reports lexical minimization as `not_measured` until resolved-call evidence
  exists.
- Updated census contract and ratchet names without weakening their thresholds.
- Tooling remains offline; no runtime hot path gains hashes, signature checks,
  provider lookup, allocation, or dispatch.
- Status: source-reviewed, deliberately unverified; census was not executed.

## 2026-08-26 multiline unsafe-authority lint follow-up

- Fixed the pure-Simple lint to recognize bounded multiline
  `@unsafe(... capabilities: [ffi])` annotations for declarations and helpers.
- Replaced substring authority checks with exact `ffi` capability-list token
  parsing, preventing reason text from granting foreign authority.
- Added regression specifications for both forms without widening authority or
  adding runtime work.
- The scan is capped at 32 annotation lines per item and stops before ordinary
  source, preserving linear lint complexity and bounded transient state.
- At this slice, Rust-seed `UnsafeBlock` HIR retained no capability list; the
  follow-up below closes that representation gap.
- Status: source-reviewed, deliberately unverified; tests were not executed.

## 2026-08-26 Rust-seed unsafe-capability retention follow-up

- Extended unsafe AST/HIR blocks with compile-time capability identifiers.
- Made raw-FFI checking require the exact `ffi` capability and reject bare or
  `raw_ptr`-only blocks.
- Preserved nested outer `ffi` authority without allowing an inner unrelated
  capability block to erase it.
- Replaced `rt_`/`spl_` prefix inference with the HIR extern-identity set, which
  already includes imported externs and aliases; pure local prefixed functions
  no longer acquire foreign authority accidentally.
- Added an O(1) empty-extern bypass to strict-profile MIR admission; actual SFFI
  modules retain one fail-fast linear HIR pass. Global gating remains sequenced
  after callsite migration so ordinary builds are not broken prematurely.
- Tagged and confined the five dedicated-host POSIX mmap/file calls to private
  always-inline owners; validated byte narrowing in the existing single pass
  and made exact size mismatch fail typed lifting.
- Made the interpreter mmap-byte handler reject arity/read failures as typed
  errors rather than legacy `Nil`, retaining one `fs::read` and direct buffer
  lift on success.
- Checked file-size `u64`-to-`i64` lifting so oversized metadata cannot wrap
  into a fabricated negative sentinel.
- Added a static authority contract. This family remains unverified/unsigned
  because no owned native rich-array provider was found.
- Kept MIR/runtime representation unchanged; capability collection is linear in
  the already-parsed header and stores one small vector per unsafe block only
  during compilation.
- Added parser, HIR, and checker regression coverage; deliberately not executed.

## 2026-08-26 UI WebSocket pure-Simple SHA-1 follow-up

- Removed four app-local raw SHA-1 declarations and their fabricated `0`/empty
  fallbacks; the write signature was not cross-lane ABI-compatible.
- Routed accept-key computation through the canonical pure-Simple RFC 6455
  handshake owner, eliminating foreign handle/return lifting in this app.
- Kept work O(n) on the bounded connection-handshake input; frame hot paths,
  network I/O count, and message allocations are unchanged.
- Routed wall-clock access through the canonical fail-closed time facade,
  removing the final raw declaration while retaining one provider call.
- Status: source-reviewed, deliberately unverified; global signed provider
  admission remains pending.
## 2026-08-26 Base64/Base64url contract follow-up

- Enforced exact interpreter arity, bounded explicit encode length, strict
  alphabet decoding, and strict UTF-8 lifting; removed nil/empty/lossy failure.
- Hardened the C oracle for null arguments, malformed length/alphabet, size
  overflow, and allocation failure, returning null rather than corrupt output.
- Tagged the two test-only raw declarations `unsafe(ffi)` and confined them to
  nullable fail-closed wrappers with input-length admission.
- Kept provider encode/decode single-pass with one output allocation; invalid
  decode frees that allocation and no valid path gains a second traversal.
- Status: source-reviewed, deliberately unverified and unsigned.
## 2026-08-26 SHA-1 return-contract follow-up

- Aligned `finish(handle) -> text?` and `finish_bytes(handle) -> [u8]?` across
  seed, interpreter, and native provider; removed the ignored out-pointer and
  packed-integer declaration mismatches.
- Native output is now a byte array rather than binary bytes tagged as text.
- Removed packed-value casting and the `nil -> 0` fallback from scalar finish;
  invalid/released handles fail closed and the scalar is a digest prefix.
- Enforced exact interpreter arity, checked explicit prefix length, checked
  handle growth, and checked native `u64 -> usize` conversion.
- Preserved one payload pass/registry operation and avoided a second validity
  lookup; scalar finish no longer formats/allocates a 40-byte hex string, and
  native digest publication uses one packed-array bulk copy.
- Status: source-reviewed, deliberately unverified and unsigned; SHA-1 is not
  admitted for security use.
## 2026-08-26 SHA-256 cross-lane return follow-up

- Aligned raw finish declarations with typed text/optional byte-array provider
  results and removed ignored out-pointer/packed-integer conversions.
- Added the exact interpreter `finish_bytes` registration; no dynamic fallback.
- Made invalid allocation/finish handles fail closed and checked native pointer
  length plus atomic handle exhaustion.
- Published native digest bytes through one packed bulk copy and derived scalar
  finish directly from eight digest bytes, eliminating hex formatting and
  per-element setter dispatch from that public path.
- Preserved one registry removal and one digest finalization; no preflight
  lookup, second lock, payload copy, or hash pass was added.
- Status: source-reviewed, deliberately unverified and unsigned.
## 2026-08-26 XXH3 legacy-boundary follow-up

- Tagged six raw XXH3 declarations `unsafe(ffi)` and confined their calls to
  the existing `XxHasher` wrapper methods.
- Replaced unchecked `u64 -> usize` pointer-length truncation with a checked
  conversion before slice construction.
- Preserved one registry operation, one lock, and one payload pass per valid
  write; added no lookup, allocation, copy, hash pass, or dispatch.
- Deferred safe publication: the legacy finish ABI aliases an invalid handle
  with the valid digest `0`; status/out v2 is required to resolve that contract.
- Status: source-reviewed, deliberately unverified and unsigned.
## 2026-08-26 transient-promotion boolean-contract follow-up

- Replaced missing-argument `false` fabrication in the Rust interpreter with a
  typed runtime error.
- Preserved genuine provider `true`/`false` results for exactly one argument.
- Ratcheted the Rust fail-closed path and the canonical `i64 -> i8` registry/C
  ABI while leaving four frontend owners explicitly unsafe.
- The valid path retains one argument bounds decision and the existing provider
  call; no allocation, copy, lookup, hash, lock, or dispatch was added.
- Status: source-reviewed, deliberately unverified and unsigned.
## 2026-08-26 transient-scope arity follow-up

- Made Rust interpreter scope begin/pause/end reject extra ABI arguments.
- Preserved valid provider booleans and canonical `() -> i8` C/registry ABI.
- Added source coverage proving invalid calls fail before scope mutation.
- Valid parse-boundary calls add one arity branch and retain one provider call;
  no allocation, copy, lookup, hash, lock, or extra traversal was added.
- Status: source-reviewed, deliberately unverified and unsigned.
## 2026-08-26 interpreter heap-metric contract follow-up

- Enforced exact arity for six interpreter heap metric handlers.
- Replaced two missing/wrong-kind fabricated zeros with typed errors while
  preserving genuine out-of-range provider zero.
- Added a static interpreter registration and contract ratchet.
- Valid diagnostic paths retain one arity/type decision and one provider read;
  no allocation, copy, lookup, hash, lock, retry, or traversal was added.
- Native typed-registry coverage remains absent, so these stay unverified and
  unsigned rather than being promoted as cross-lane safe.
## 2026-08-26 memory-attribution contract follow-up

- Enforced exact interpreter arity/types for enabled, set-owner, report, and
  report-print.
- Removed fabricated report limit `16` and wrong-type successful set-owner no-op.
- Preserved valid owner-report generation, sorting, allocation, and printing.
- Added a static lane-split ratchet: native set-owner is `(ptr,len)`, interpreter
  is lifted text, and report functions remain without typed native registration.
- Valid paths add only arity/type decisions before existing work; no provider
  lookup, hash, lock, retry, or extra report traversal was added.
- Status: source-reviewed, deliberately unverified and unsigned.
## 2026-08-26 memory-profile arity follow-up

- Enforced exact zero-argument contracts for four interpreter profiling APIs.
- Preserved genuine harden, guard, ABI-version, and feature results.
- Added source coverage and a static ratchet that refuses to equate interpreter
  registration with missing typed native registry/header coverage.
- Valid diagnostic calls add one arity branch before unchanged provider work;
  no allocation, copy, lookup, hash, lock, retry, or traversal was added.
- Status: source-reviewed, deliberately unverified and unsigned.
## 2026-08-26 Unix-socket service contract follow-up

- Tagged all six raw service socket declarations `unsafe(ffi)`.
- Corrected close from fabricated boolean shape to its `i32` errno contract.
- Enforced exact interpreter arity/types for listen/accept/send/recv/close and
  rejected negative receive sizes before allocation.
- Replaced receive failure/invalid-UTF-8 empty fabrication with typed errors;
  valid UTF-8 now reuses the allocated buffer instead of lossy-copying it.
- Preserved valid-path matches, locks, syscalls, and allocation count; no hash,
  registry lookup, retry, or extra network dispatch was added.
- Kept native recv pointer/out-length versus Simple text lifting explicitly
  unverified/unsigned pending a generated descriptor wrapper.
## 2026-08-26 QMP/client socket provider follow-up

- Enforced exact transport for connect/write/read-until/close.
- Rejected negative/out-of-range buffer lengths and stop bytes before I/O.
- Replaced read errors/invalid UTF-8 empty fabrication with typed errors while
  retaining genuine EOF empty text and genuine `-1`/`false` OS outcomes.
- Reduced initial read capacity to `min(max, 256)` and reused the buffer for
  valid UTF-8; no lookup, retry, extra syscall, or lossy copy was added.
- Raw Simple caller declarations remain the next confinement slice.
## 2026-08-26 QMP/SPM raw-call confinement follow-up

- Tagged eight duplicate raw socket declarations across QMP/SPM `unsafe(ffi)`.
- Confined them to four non-exported always-inline owners per module.
- Preserved every caller status branch and exact raw call count/order.
- Added no allocation, copy, hash, lookup, lock, retry, or dynamic dispatch.
- Native receive descriptor lifting remains explicitly unverified/unsigned.
## 2026-08-26 interpreter diagram-contract follow-up

- Enforced declared arity across twelve diagram interpreter handlers.
- Removed undeclared array filtering and wrong-type/nil-to-absence conversion.
- Validated the free-string handle before its interpreter managed-memory no-op.
- Used one always-inlined arity helper; valid generation/tracing work, data
  structures, allocations, and algorithmic complexity remain unchanged.
- Raw Simple unsafe confinement and native pointer/return lifting remain
  explicitly unverified and unsigned.
## 2026-08-26 diagram raw-declaration follow-up

- Tagged all twelve raw seed diagram declarations `unsafe(ffi)`.
- Confined ten live calls to their existing higher-level lexical boundaries.
- Corrected free-string handle width from `i32` to `i64`.
- Refused the unsafe shortcut of adding diagram functions to C-string lowering;
  native `(ptr,len)` adapters remain required before safe promotion.
- Added no marshalling, allocation, copy, lookup, or dispatch on valid calls.
- Status: source-reviewed, deliberately unverified and unsigned.
## 2026-08-26 span-handle contract follow-up

- Tagged all six untyped span-handle declarations `unsafe(ffi)`.
- Enforced exact arity, non-negative/platform-sized fields, and `end >= start`.
- Made handle allocation fail on ID overflow and release fail on unknown/double
  free instead of reporting successful unit.
- Preserved one registry operation per valid create/access/free and added no
  lookup, allocation, copy, hash, retry, or traversal.
- Typed native registry coverage remains absent; status is unverified/unsigned.
## 2026-08-26 SHA-256 handle-contract follow-up

- Enforced exact arity for new/write/finish/reset/free interpreter handlers.
- Removed malformed-length fallback-to-full-payload hashing.
- Rejected non-`i64` handles and atomic handle-counter overflow.
- Tagged six raw seed declarations `unsafe(ffi)`; free stays explicitly
  idempotent because both providers define that semantic.
- Confined raw calls to the six existing `Sha256Hasher` method boundaries;
  seed integer carrier versus interpreter array transport remains unresolved.
- Preserved one payload pass and one registry operation per valid call; no
  extra payload copy, traversal, lookup, hash pass, lock, or dispatch was added.
- Status: source-reviewed, deliberately unverified and unsigned.

## 2026-08-26 mmap-byte provider identity correction

- Corrected the stale claim that no owned native provider exists: Rust exports
  `rt_file_mmap_read_bytes`, and pure-Simple/C-bootstrap provide the sibling
  byte-reader implementation.
- Changed the dedicated-host raw declaration to `[u8]?`, preserving provider
  `NIL` as explicit absence and lifting it to `Result.Err`; a valid empty array
  remains a successful value.
- Matched the provider byte-array element type and removed the former O(n)
  i64-to-u8 conversion, second allocation, and payload copy.
- Keep status-plus-owned-output as the eventual versioned registry contract;
  the nullable bridge is an exact existing ABI but not signed admission.
- Reject extra stat/existence probes, duplicate reads, per-byte foreign calls,
  and sentinel payloads: they add races, I/O, dispatch, or ambiguity.
- Improve the current envelope to one read and the provider-owned output only;
  keep signature and evidence verification at admission, never on the call
  path.
- Status: source-reviewed, deliberately unverified and unsigned.

## 2026-08-26 span-handle export minimization

- Confirmed the six interpreter span-handle symbols have no Simple consumers.
- Removed both direct-module and aggregate exports while retaining private,
  explicitly `unsafe(ffi)` declarations and the hardened interpreter provider.
- Added a static authority contract that rejects raw re-export and new
  interpreter callsites outside the owner.
- Avoided manufacturing an ownership wrapper for an unused API, so there is no
  new owner allocation, lookup, branch, copy, or provider dispatch.
- A future consumer must first introduce a typed non-copying owner with explicit
  close/drop semantics; raw i64 handles must not be re-exported.
- Status: source-reviewed, deliberately unverified and unsigned.

## 2026-08-26 font SFFI authority confinement

- Tagged all twelve raw font/bitmap declarations `unsafe(ffi)` in the canonical
  no-GC sync owner.
- Confined all existing calls to nine lexical unsafe regions inside the current
  high-level font and glyph wrappers; raw symbols remain unexported.
- Preserved the exact provider-call count and order for load, glyph creation,
  metrics, pixel reads, and release.
- Added a static ratchet for declaration/call counts and the one-call pixel and
  glyph hot paths; no allocation, copy, scan, hash, lookup, or dispatch added.
- Keep the family unsafe until bitmap handles become typed non-copying owners
  with generation/liveness validation and provider admission is signed.
- Status: source-reviewed, deliberately unverified and unsigned.

## 2026-08-26 gamepad boundary deduplication

- Replaced the app-local 20-declaration/roughly-400-line gamepad copy with an
  export-only facade over the canonical Pure-Simple no-GC sync owner.
- Preserved the complete public type/function surface and runtime-family facade
  direction; no C/Rust implementation replaces Pure Simple.
- Extended the existing authority ratchet to reject raw declarations, raw
  calls, and duplicate wrapper functions in the app facade.
- Preserved canonical provider-call counts and all polling, event, rumble, and
  deadzone behavior; export resolution adds no runtime allocation, lookup,
  branch, copy, or dispatch.
- Keep all 20 symbols unsafe/unavailable until real typed providers are
  registered, then require signed exact-artifact admission before promotion.
- Status: source-reviewed, deliberately unverified and unsigned.

## 2026-08-26 volatile/MMIO boundary deduplication

- Replaced the app-local eleven-declaration volatile/MMIO implementation with
  an export-only facade over the canonical Pure-Simple no-GC owner.
- Moved the three native-required u64 read/write/full-barrier helpers to the
  canonical owner and tagged/confined their raw operations with `ffi` and
  `raw_ptr` authority.
- Preserved one direct provider operation for each host daemon call and added no
  runtime branch, allocation, lookup, copy, hash, or dispatch.
- Registered the three already-implemented interpreter fences, tagged all
  eleven raw declarations, and confined all generic/native-required calls.
- Removed hardcoded-unavailable branching and all eleven fabricated zero/no-op
  fallbacks; missing providers now fail at resolution/link/admission.
- Reduced each generic hot path from availability branch plus fallback/provider
  call to exactly one provider call, with no allocation, lookup, copy, or hash.
- Next migrate raw-address callers to capability-correct MMIO owners and add
  signed admission while keeping verification off the MMIO hot path.
- Status: source-reviewed, deliberately unverified and unsigned.

## 2026-08-26 HTTP/WebSocket boundary deduplication

- Replaced both app-local HTTP implementations (52 raw declarations and about
  one thousand repeated lines) with export-only facades over the canonical
  Pure-Simple no-GC sync owner.
- Preserved the full API and live `app.io.http_ffi` consumer; canonical handle
  validation is stricter for negative client/server/WebSocket handles.
- Updated both HTTP authority audits to require one 26-declaration owner and two
  app facades with no raw declarations, calls, or wrapper bodies.
- Preserved 29 canonical provider calls and added no request-path allocation,
  lookup, branch, copy, hash, or dispatch.
- Keep the family unsafe until incomplete providers and WebSocket nullable/error
  contracts are replaced and exact artifacts receive signed admission.
- Status: source-reviewed, deliberately unverified and unsigned.

## 2026-08-26 SQLite boundary deduplication

- Replaced both app-local SQLite implementations (54 raw declarations and more
  than one thousand repeated lines) with high-level-only facades over the
  canonical Pure-Simple no-GC owner.
- Preserved the live `app.io.context_ops` API while intentionally withholding
  raw `rt_sqlite_*` handles from both app export surfaces.
- Updated both SQLite audits to require one 27-declaration/26-call owner and two
  export-only facades with no raw declarations, calls, or wrapper bodies.
- Added no query-path call, allocation, lookup, copy, hash, or dispatch.
- Keep PureDatabase preferred; migrate legacy SQLite done/error/null contracts
  to typed status/out and require signed exact-artifact admission before any
  safe promotion.
- Status: source-reviewed, deliberately unverified and unsigned.

## 2026-08-26 legacy regex boundary deduplication

- Replaced the app legacy regex implementation with an export-only facade over
  the API-compatible no-GC async owner.
- Removed eight duplicate raw declarations and the app copy's repeated-array
  concatenation; the retained find-all path uses amortized-linear `push`.
- Tagged all eight retained declarations and confined all nine raw calls.
- Added a ratchet for provider registry presence, raw-free facade shape, and
  linear find-all accumulation; no wrapper call or runtime dispatch added.
- Kept the distinct no-GC sync `simple_regex_*` API separate to avoid wrapper
  overhead and semantic drift.
- Next replace no-match/provider-failure ambiguity and feature-gated stub
  outputs with typed results and signed exact-artifact admission.
- Status: source-reviewed, deliberately unverified and unsigned.

## 2026-08-26 compiler minimal-runtime unsafe-surface restoration

- Restored explicit `unsafe(ffi)` authority on all 42 raw declarations and all
  42 direct wrappers after a snapshot regressed the implementation while
  retaining its authority scripts.
- Preserved the newer bounded no-follow file-read API and included it in the
  same one-declaration/one-wrapper policy.
- Preserved nullable environment lookup and deep-array release results rather
  than fabricating integer zero.
- Retained one direct provider operation per wrapper; no allocation, copy,
  lookup, hash, branch, generic dispatch, or registry work was added.
- Provider closure remains incomplete (15 both lanes, 3 native-only, 6
  interpreter-only, 18 neither); resolve or remove the 27 asymmetric/missing
  contracts before safe promotion, then require signed exact-artifact
  admission.
- Status: source-reviewed, deliberately unverified and unsigned.

## 2026-08-26 RuntimeValue boolean registry closure

- Add exact native `[I64] -> [I8]` registry contracts for boolean extraction
  and the four RuntimeValue type predicates whose Rust exports and interpreter
  handlers already exist.
- Preserve semantic `bool`; do not widen the Simple API to an integer
  workaround.
- Add only compile-time signature rows, with no hot-path branch, conversion,
  allocation, copy, lookup, hashing, or dispatch.
- Remaining minimal-facade closure is 20 both lanes, 3 native-only, 1
  interpreter-only, and 18 neither; next reconcile the one `rt_file_delete`
  pointer/length versus text ABI before registration.
- Keep all functions unsafe and unsigned until exact-artifact admission and
  cross-lane semantic evidence exist.
- Status: source-reviewed, deliberately unverified and unsigned.

## 2026-08-26 network boundary checkpoint

- Replace two GC 41-declaration network copies with compile-time export
  facades; retain no wrapper hop or per-call allocation, lookup, copy, branch,
  hash, lock, or dispatch.
- Keep the current no-GC async resolution owner and the historical no-GC sync
  surface temporarily; collapsing the latter would remove its TCP exports.
- Treat its 18 providerless UDP/HTTP/URL declarations as unresolved safety
  debt, not as implementations and not as candidates for cosmetic safe tags.
- Next reroute URL encoding/decoding to the existing Pure-Simple owner, replace
  HTTP with a typed live transport, and design UDP around scalar/status-out
  runtime contracts rather than passing high-level `UdpSocket` objects across
  the ABI.
- Require exact-artifact signed admission only at provider load time; never add
  signature checking, registry lookup, or hashing to the network hot path.
- Remaining production debt after this pass: 4,274 unsafe-tag gaps, 6,076
  contract gaps, and zero signed-admitted declarations.
- Status: source-reviewed, deliberately unverified and unsigned.

### Pure-Simple URL codec follow-up

- Replace both owners' `url_encode`/`url_decode` foreign declarations with
  direct exports from their existing Pure-Simple RFC 3986 modules.
- Preserve the public names with no forwarding wrapper and no per-call
  allocation, lookup, copy, branch, hash, lock, or dispatch beyond the codec's
  existing algorithm.
- Remaining network providerless identities: 16 (14 UDP, HTTP request, and URL
  parse). Remaining production debt: 4,270 unsafe-tag gaps, 6,072 contract
  gaps, and zero signed-admitted declarations.
- Status: source-reviewed, deliberately unverified and unsigned.

### Pure-Simple URL parser follow-up

- Remove both remaining `url_parse` foreign declarations and adapt each
  `net.Url.parse` variant from its matching Pure-Simple fail-closed parser.
- Preserve the public `Result<Url, SimpleError>` API and construct only the
  required public result after the existing O(n) parse; add no foreign
  marshalling, registry lookup, signature check, hash, lock, or dispatch.
- Remaining network providerless identities: 15 (14 UDP and HTTP request).
  Remaining production debt: 4,268 unsafe-tag gaps, 6,072 contract gaps, and
  zero signed-admitted declarations.
- Status: source-reviewed, deliberately unverified and unsigned.

### Canonical UDP contract-closure follow-up

- Close all eleven `rt_io_udp_*` identities across the C provider, Rust
  provider, interpreter registry, runtime-symbol manifest, and typed JIT
  registry before rerouting the legacy network API.
- Preserve semantic booleans with exact i8 ABI instead of widening the public
  API to integer status workarounds.
- Bound receive allocations to the UDP payload limit, return nil on provider
  failure, and make C `recv_from` return the declared `(bytes,address)` tuple.
- Use packed interpreter byte arrays, avoiding one generic value per received
  byte and matching the native lanes' data layout.
- Retain one socket operation and one required bounded receive allocation; add
  no registry lookup, signature verification, hash, retry, copy, or generic
  dispatch to the hot path.
- Next migrate/remove the fourteen providerless `udp_socket_*` identities,
  then address multicast API compatibility without duplicating raw owners.
- Status: source-reviewed, deliberately unverified and unsigned.

#### Legacy UDP surface removal

- Add typed multicast loop/join/leave contracts to the canonical scalar-handle
  owner across C, Rust, interpreter, JIT registry, headers, and linker closure.
- Replace `std.net.udp` with a compile-time facade over the typed `Result` API;
  remove all 28 providerless `udp_socket_*` declaration occurrences.
- Preserve one handle lookup plus one socket operation for membership/options;
  use stack-only C address parsing and add no wrapper allocation, registry
  lookup beyond the canonical handle lookup, hash, signature check, generic
  dispatch, or payload copy.
- Remaining legacy network providerless identities: one (`http_request`).
  Remaining production debt: 4,240 unsafe-tag gaps, 6,058 contract gaps, and
  zero signed-admitted declarations.
- Status: source-reviewed, deliberately unverified and unsigned.

#### Language-aware census reporting

- Extend `sffi-contract-inventory.shs` to report declaration and `rt_` totals
  per observed provider language, with unsafe-tagged, freshly signed-admitted,
  and untouched counts kept as separate dimensions.
- Correct the symbol summary terminology: it now distinguishes symbols whose
  declarations are all unsafe-tagged from symbols with at least one unsafe-tag
  gap. The former report called the latter `unsafe_tagged`, which inverted the
  meaning and could mislead a migration review.
- Language provenance remains observational; it never upgrades ABI safety or
  cryptographic admission. Signed admission still requires a fresh verifier
  join on provider, symbol, and exact source-signature identity.
- Status: source-reviewed; the census was not executed in this tranche.

#### Lossless HTTP v2 boundary and legacy providerless removal

- Add `rt_http_request_v2(method, url, headers, body_bytes, timeout_ms)` with a
  total `(status, reason, raw_headers, body_bytes, transport_error)` result in
  native C and the Rust interpreter. Status `-1` is reserved for contract or
  transport failure; HTTP 4xx/5xx remain ordinary typed responses.
- Preserve arbitrary binary request/response bodies and the response reason and
  headers that the v1 text tuple discarded. Bound response collection to
  64 MiB, header metadata to 1 MiB/1,024 fields, and status reason to 8 KiB;
  reject malformed header/body/timeout inputs before I/O.
- Lift the raw tuple once in the canonical no-GC sync `HttpClient`, implement
  configured redirect limits, and replace async/GC copies with compile-time
  facades. Remove both providerless high-level-object `http_request` externs.
- Hot path has no admission hash/signature/symbol lookup or generic dispatch.
  The v2 lane adds only the response metadata/body allocations required by its
  public API; legacy v1 callers do not allocate returned metadata.
- Estimated production inventory after this source change: 7,107 declarations,
  2,869 unsafe-tagged, 4,238 unsafe-tag gaps, 6,056 contract gaps, zero
  providerless legacy network identities, and zero signed admission.
- Status: source-reviewed, deliberately unverified and unsigned.
- Native core C still supports `http://` only and returns a typed transport
  error for `https://`; the interpreter provider uses ureq/TLS. Cross-lane
  HTTPS parity remains a separate TLS-provider migration requirement, not a
  reason to fabricate a response or silently downgrade the scheme.
