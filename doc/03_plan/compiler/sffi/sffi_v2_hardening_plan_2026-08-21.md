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
`doc/08_tracking/bug/data/sffi_contract_inventory_2026-08-21.tsv`.

Current evidence:

- 3,959 distinct extern symbols;
- 14,908 declaration sites;
- 14,391 sites have neither an explicit FFI-unsafe tag nor a local contract;
- 515 sites declare a typed/documented contract but lack the unsafe tag;
- 2 sites carry an unsafe tag but still lack a return/ownership contract;
- among `rt_*`/`spl_*` declarations, 1,855 sites reference symbols classified
  genuinely missing and 321 are backed only in owned C runtime source.

These are migration inputs, not 14,908 independent implementations. The next
tooling step groups declarations by canonical symbol owner, rejects conflicting
signatures, and converts compatibility modules to re-export the canonical
no-GC owner. Safety is then discharged once per symbol/ABI hash while every raw
call site retains a minimal lexical `unsafe(ffi)` scope.

Performance constraint: the legacy native integer call remains allocation-free.
The lint guard extracts its body and fails if `rt_array_new`, `Vec`, maps,
mutexes, `dlsym`, or other lookup/allocation primitives enter that hot path.
Typed sealed thunks remain the production target; pair-returning checked arrays
are migration/interpreter adapters, not the final critical hot path.

## Requirement decision

The user selected the recommended SFFI v2 architecture: versioned stable C ABI
shim, generated unsafe raw declaration, generated validation/lift wrapper, and
safe typed API. P0/P1 requirements and NFRs are final in the linked documents.
Detailed P4 signing/trust deployment and P5 migration scheduling remain planned
decisions; they must not delay P0 fail-closed behavior or be claimed complete.
