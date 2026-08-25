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

Checkpoint: the compiler core WFFI facade now uses checked load/get operations
and tags every remaining raw all-`i64` call wrapper with `unsafe(ffi, raw_ptr)`.
The call wrappers retain their existing allocation/dispatch shape; no defensive
branch was added to the legacy per-call path. Their long-term replacement is a
generated typed thunk, not implicit scalar conversion.

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

Checkpoint: the first source-ledger consolidation removed all 26 duplicate
Simple `rt_mkdir_p` declaration rows, including mirrored specs, and removed the
obsolete unconditional LLVM declaration. Callers now use the canonical
`std.io_runtime.mkdir_p` wrapper, whose only raw operation is the existing
scoped `rt_dir_create_all` call. The focused SFFI lint was repaired to define
its previously missing negative-pattern helper and now rejects any future raw
Simple `rt_mkdir_p` declaration. The lint passed once. No per-call hashing,
lookup, allocation, copy, or new loop was introduced; runtime performance
measurement remains blocked on the admitted self-hosted compiler.

Checkpoint: all 20 raw Simple `rt_sleep_ms` declarations were replaced by the
canonical blocking `thread_sleep` wrapper and a compatibility Simple function;
the boundary remains one scoped `rt_thread_sleep` call. The nullable
`rt_env_cwd` contract is now owned by `std.io_runtime` as `text?`, with a total
`"."` lift. That removes the previous `pwd` subprocess and prevents provider
nil from entering non-optional text. Bootstrap-library mirrors use the same
optional contract and lexical authority. The refreshed full ledger is 12,070
`rt_*` declaration rows / 3,171 distinct symbols, with 10,835 / 2,243 still
untouched and zero production admissions.

Checkpoint: the canonical TCP owner now tags 23 raw descriptor/read/write/
option contracts and scopes every direct call to one FFI expression. The read
ABI no longer fabricates empty bytes on failure: C, Rust, interpreter, and all
20 Simple declarations use nil-for-error and empty-for-EOF. Safe `Result`
wrappers lift nil to an error; server loops deliberately treat an error as
connection termination. The source ledger advanced to 1,005 unsafe-tagged
`rt_*` declaration rows / 720 tagged symbols, leaving 10,796 / 2,228 untouched.
Focused Rust tests and the C compile gate passed once. Successful read call
count, allocation shape, and algorithmic complexity are unchanged.

Checkpoint: raw TCP bind, accept, and accept-timeout declarations and their
owned call sites now have explicit narrow FFI authority. No wrapper, lookup,
allocation, or additional runtime branch was introduced. Accept-timeout is not
yet safe because its negative sentinel cannot distinguish timeout from provider
failure. The refreshed row ledger is 12,070 total, 1,057 unsafe-tagged, 754
contract-documented, 485 unsafe-minimized, and 10,744 untouched. The provider
definition census is C 2,378, Rust 2,178, Simple 576, and C++ 219. Exact-artifact
verified-and-signed admission remains zero.

Checkpoint: TCP status booleans now have one ABI across C, Rust, Simple, and
native codegen. Timeout setters use a scalar, allocation-free sentinel ABI and
reject malformed interpreter bridge values instead of treating them as “clear
timeout.” Focused C compilation and Rust provider/interpreter/codegen tests
passed. The current ledger is 12,070 declaration rows, 1,148 unsafe-tagged,
754 contract-documented, 485 unsafe-minimized, 10,653 untouched, and zero
exact-artifact verified-and-signed admissions.

Checkpoint: contract-reason parsing now counts explicit failure/null/family
semantics without promoting source claims to evidence. The updated ledger is
12,070 total rows, 1,163 unsafe-tagged, 883 contract-documented, 614
unsafe-minimized, 10,638 untouched, and zero verified-and-signed. TCP accept
and connect budgets now fail closed, native signatures are registered, the C
connect timeout performs bounded nonblocking polling, and SimpleOS holds one
netstack owner value across its bounded accept loop.

For each row, prefer a pure-Simple owner. Otherwise require either:

1. admitted exact evidence plus a typed safe wrapper; or
2. the smallest lexical `unsafe(ffi)` boundary plus an executable typed contract.

Unverifiable in-process providers remain unsafe or move behind a process/Wasm
boundary. Mass tagging is prohibited because it would hide unreviewed debt.

Checkpoint: the UDP scalar-option tranche aligns `connect`, broadcast,
read-timeout, and nonblocking as semantic boolean contracts across C, Rust,
interpreter, Simple, and native codegen. Optional timeout lowering is performed
once in the safe wrapper and does not transport an Option object across the ABI.
Focused C/Rust/compiler/static checks passed, with no per-call allocation,
lookup, hashing, or generic dispatch added. The refreshed source-only ledger is
12,038 `rt_*` declaration rows / 3,179 symbols: 1,187 rows unsafe-tagged, 562
contract-documented and unsafe-minimized, 10,581 untouched, and zero
exact-artifact verified-and-signed. Full provider-language provenance and
self-hosted optimizer evidence remain pending the admitted Stage-4 toolchain.

Checkpoint: UDP receive now preserves `nil` versus a valid empty datagram, and
`recv_from` returns the declared `(bytes, peer)` tuple instead of a bytes-only
fabrication. Send failures are negative while zero remains a valid empty send.
Native receive writes directly into one bounded packed buffer and frees it on
failure; Rust formats peer addresses on a fixed stack buffer. The bytes-only
benchmark avoids peer tuple/text allocation. Focused C/runtime/compiler/static
evidence passed. The source-only ledger is now 12,038 `rt_*` rows / 3,179
symbols: 1,200 unsafe-tagged, 568 contract-documented and unsafe-minimized,
10,572 untouched, and zero exact-artifact verified-and-signed.

Checkpoint: the common ECDSA P-256 wrapper now consumes only checked signing
and verification contracts and exposes `Result`, preserving `Ok(false)` solely
for a real cryptographic mismatch. Malformed bridge values, keys, SPKI, and
signature lengths are errors; empty signatures are never safe values. Raw calls
are lexically scoped to one `unsafe(ffi)` statement. The static guard and source
check passed without adding hot-path lookup, hashing, copying, or allocation.
The executable spec is blocked upstream by the unrelated
`env_access_host.spl` parser failure and the available tool reports itself as a
Rust bootstrap seed. The source-only ledger is 12,038 `rt_*` rows / 3,179
symbols: 1,202 tagged, 650 contract-declared, 10,570 untouched, and zero
exact-artifact verified-and-signed.

Checkpoint: removed the unresolved P-384/P-521 signing and verification SFFI
surface. No provider, interpreter registration, or codegen contract existed;
the canonical engines are already pure Simple. The host-key dispatcher is now
typed `Result` and directs these algorithms to those owners rather than
fabricating `false`. Static and source checks pass, with no foreign dispatch or
new hot-path work. The ledger is now 12,034 `rt_*` rows / 3,175 symbols: 1,198
tagged, 646 contract-declared, 10,570 untouched, and zero exact-artifact
verified-and-signed.

Checkpoint: removed three unused raw RSA/Ed25519 verification declarations from
the SSH session layer and ratcheted direct crypto authority out of those files.
Focused static and source checks pass with zero runtime/performance change. The
ledger is 12,031 `rt_*` rows / 3,175 symbols: 1,198 tagged, 646
contract-declared, 10,567 untouched, and zero exact-artifact signed/admitted.

Checkpoint: removed eight legacy raw declarations from the canonical signature
facade. Its RSA/Ed25519/P-256 public names now return checked `Result` values;
malformed input/provider failure cannot become empty signatures or `false`.
Primary specs were migrated to explicit success/error assertions. Static and
facade source checks pass; executable SSpec is blocked by the unrelated
`env_access_host.spl` parser failure. No provider-call, allocation, copy,
lookup, or hashing regression was introduced. The ledger is 12,023 `rt_*`
rows / 3,172 symbols: 1,190 tagged, 638 contract-declared, 10,567 untouched,
and zero exact-artifact signed/admitted.

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
