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

Checkpoint: bootstrap source lowering now shares the `E-SFFI-016` fail-closed
contract. Unit fallthrough remains operand-less; non-unit stub or flat-body
fallthrough records a fatal diagnostic and never constructs typed zero. The
validator runs only on fallthrough, so valid function return paths gain no
branch, allocation, or dispatch. Self-hosted behavioral verification remains
blocked by the unavailable admitted current-source runtime.

Checkpoint: the canonical dynamic loader no longer returns an invalid
`DynLib(handle: 0)` from `open`, and legacy singleton dispatch no longer turns
provider or malformed-name failures into integer zero. Optional load remains
the explicit ordinary-unavailability API, so boolean availability callers keep
their semantics without conflating a valid foreign zero with bridge failure.
Candidate probing still performs one load attempt per candidate and admitted
hot calls gain no additional lookup or allocation.

Checkpoint: the LLVM adapter no longer creates an invalid `DynLib` when its
provider is absent and no longer caches or invokes a null symbol. Provider and
first-resolution failures are fatal; the established cached-symbol hot path is
unchanged and gains no branch, lookup, allocation, or copy.

Checkpoint: the Rust interpreter dynload bridge now uses its existing
`Result<Value, CompileError>` channel for malformed paths, null handles,
missing libraries/symbols, and unsupported platforms. It no longer converts
those failures to integer zero. Success performs the same single OS call and
value lift; the added checks are boundary failure checks, not hot foreign-call
dispatch work.

Checkpoint: the interpreter `i64` bridge no longer coerces `bool` to `1/0`.
Both the explicit WFFI bridge and legacy dynamic dispatcher now match the
native checked bridge and reject every non-integer value; typed boolean ABI
support must use a boolean thunk instead of changing the source value's type.
This removes conversion work rather than adding hot-path overhead.

Checkpoint: the focused SFFI guard now ratchets interpreter dynload errors,
boolean ABI identity, proofless C/C++ optimizer non-null attributes, and
unchecked Rust `NonNull` lifts. Its first run exposed a string-builder lift
that converted invalid handles/null data to empty text. The lift now preserves
valid empty text, rejects invalid handles/data/UTF-8, copies exactly once, and
releases the consumed runtime string. The repaired focused guard passed once on
2026-08-25; this is narrow source-contract evidence, not global SFFI proof.

Checkpoint: C owner/fallback, Rust native, interpreter, codegen, and canonical
Simple loader now share `spl_dlopen_checked(path, out_handle) -> status`.
Every provider-load attempt initializes output to zero, returns success only
with a non-null handle, and lifts the outcome into `Result` or deliberate
optional availability. Legacy `spl_dlopen` remains an unsafe compatibility
shim. The checked work happens once during provider loading; cached foreign
calls receive no new branch, allocation, lookup, or signature work.

Verification checkpoint: the expanded SFFI null/signature guard passes. The
runtime duplicate-owner audit reports all seven `same` bodies, including the
checked loader and resolver, as non-divergent. Its overall result remains red because twelve
unrelated runtime/runtime-native or runtime/legacy-core duplicate symbols are
above the current baseline; those symbols are outside this lane and were not
silently folded into the SFFI change.

Checkpoint: the same status/out contract now covers symbol resolution through
`spl_dlsym_checked(handle, name, out_symbol)`. Canonical Simple call and cached
slot resolution use the checked result; raw `sym`/`spl_dlsym` remain explicitly
unsafe compatibility surfaces for callers still awaiting migration. Each
checked resolution initializes output to zero and rejects null handles, empty
or malformed names, and null results. Cached slot invocation remains a direct
pointer call with no added work.

### 3. Complete resolved-HIR inventory

Checkpoint: the bounded source ledgers now report 12,128 `rt_*` declaration
rows, 3,173 distinct `rt_*` symbols, 951 unsafe-tagged declaration rows, 10,907
untouched declaration rows, and zero signed/admitted symbols. The call-authority
ratchet fails with 19,494 missing-authority sites. These measurements prioritize
the migration but do not satisfy this step's resolved-HIR exit criterion.

Checkpoint: resolved-HIR identity now also follows `MethodResolution` for
instance, trait, UFCS/free-function, and static call forms. The same symbol-ID
rule feeds lexical safety enforcement, while unresolved `rt_`/`spl_` method
candidates make inventory completeness fail closed. This adds compiler/audit
work only; generated runtime calls gain no lookup, branch, allocation, or copy.
Behavioral coverage is present but remains unexecuted until an admitted
self-hosted runtime is available.

Checkpoint: resolved fields and indirect callable values now retain the raw
callable type marker through both inventory and lexical enforcement. Indirect
sites have a dedicated count rather than being mislabeled as a distinct
provider symbol.

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
