# SFFI universal admission: next implementation plan

**Research:** `doc/01_research/local/sffi_universal_admission_next_2026-08-25.md`  
**Requirements:** existing selected SFFI v2 feature/NFR requirements  
**Status:** planned; universal safety/signing/verification is not claimed

## Ordered closure plan

### 1. Canonicalize loader ownership

- Replace the duplicate `std.ffi.dynamic_versioned` implementation with an
  export-only facade over `std.sffi.dynamic_versioned`.
- Tag the smallest canonical versioned-load, symbol-resolution, and cache
  operations with explicit `unsafe(ffi[, raw_ptr])` authority.
- Preserve API, provider search order, cache keys, and call cardinality.

Exit: one implementation owner, no new lookup/allocation on any call path.

Checkpoint: source implementation is complete but unverified. The compatibility
file is now an export-only facade, the canonical exported surface is explicitly
public, and load/symbol operations carry minimal unsafe authority. The available
release path identified itself as the bootstrap seed and failed before the
focused spec, so self-hosted acceptance and optimizer evidence remain open.

### 2. Remove remaining fabricated returns

- Replace bootstrap non-unit missing-return zero synthesis with the same total
  return-contract failure used by normal MIR lowering.
- Make unresolved/null provider paths typed errors or remain explicitly unsafe;
  never manufacture zero, false, nil, empty text, or empty arrays.

Exit: interpreter/bootstrap/native negative cases agree on diagnostic category.

### 3. Complete resolved-HIR inventory

- Extend compiler-owned extern identity through aliases, re-exports, methods,
  generated declarations, and indirect callable values.
- Require `hir_complete == true` before workspace totals are authoritative.
- Reconcile declaration/call baselines without increasing them; retain the fast
  source scanner as a partial lower-bound diagnostic.

Exit: commit-bound module/family, declaration, symbol, and live-call reports with
no mixed units or ambient-call gap.

### 4. Create one production admission owner

- At `NativeLibManager.add_shared/add_system`, verify a configured trust policy,
  canonical signed manifest, exact artifact snapshot, ABI registry, source/build/
  compiler identities, and required verification receipts before mapping or
  publication.
- Bind the verified token to the exact opened bytes and provider generation.
- Make raw `spl_dlopen` delegate to this owner or remain explicit development-
  only unsafe and fail closed in hardened/critical profiles.
- Reject non-Linux critical dynamic admission until equivalent immutable-object
  loading exists.

Exit: no production provider can publish a symbol without an unforgeable,
artifact-bound admission token.

### 5. Publish typed cached slots

- Generate one slot family per canonical ABI registry signature.
- Validate the complete closure before atomic publication.
- Migrate one bounded integer-only production provider first, then status/out,
  float, descriptor, resource, callback, and aggregate families separately.
- Bind destructor, allocator, nullability, sentinel, unwind, and thread policy.

Exit: hot calls use direct cached slots and allocate nothing for scalar/opaque
handle contracts.

### 6. Migrate or isolate every remaining row

For each row, prefer a pure-Simple owner. Otherwise require either:

1. admitted exact evidence plus a typed safe wrapper; or
2. the smallest lexical `unsafe(ffi)` boundary plus an executable typed contract.

Unverifiable in-process providers remain unsafe or move behind a process/Wasm
boundary. Mass tagging is prohibited because it would hide unreviewed debt.

### 7. Verify once, then stop

- Run sabotage and parity across interpreter, JIT, native, sealed dynload, and
  SimpleOS only after the admitted current-source compiler exists.
- Compare identical before/after startup, representative call latency, peak RSS,
  allocations, and generated call shape.
- Reject any hot-path hash, signature, path/name lookup, map lookup, generic
  decode, mutex, or allocation regression.
- Keep the existing verification report at `FAIL` until full-scope evidence
  supersedes it.

## Ownership

| Lane | Scope | Acceptance owner |
|---|---|---|
| compiler | return semantics, resolved identity, safety severity | `/root` |
| library | canonical dynload owner, typed slots, resource contracts | `/root` |
| loader | trust policy, immutable artifact, provider generation | `/root` |
| evidence | manifests, signatures, receipts, sabotage | `/root` |
| performance | same-tree timing/RSS/allocation/call-shape gate | `/root` |

Read-only research sidecars were used for compiler, library, and documentation
audits. Merge owner and final highest-capability reviewer: `/root`.
