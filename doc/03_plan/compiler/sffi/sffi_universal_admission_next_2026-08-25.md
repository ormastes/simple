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

Stop-the-line checkpoint: bootstrap atomics cannot be promoted by unsafe tags.
Their source/provider argument counts and boolean/compare-exchange results
diverge, flag inspection mutates state, spin-loop closure is incomplete, and
the provider is mutex/map-backed rather than lock-free. Fix the ABI and boolean
semantics first under the single-call hot-path gate documented in
`doc/08_tracking/bug/bootstrap_atomic_sffi_abi_and_semantics_2026-08-26.md`.

Source-resolution checkpoint: bootstrap atomics now use exact provider-owned
SeqCst signatures, boolean compare-exchange, non-mutating flag load, and closed
C/Rust/interpreter/native identities. Each ordinary operation remains one
provider call; no contention-path reload, wrapper allocation, lookup, retry,
hash, or signature work was added. Manual release and unproven `AtomicRef`
casts remain unsafe. Dynamic performance/correctness evidence, replacement of
the Rust mutex/map compatibility provider, artifact signatures, and admission
receipts remain open.

Checkpoint: the bootstrap sandbox builder removed seven unused raw declarations
and confines all fifteen live reset/configure/apply operations to individual
lexical `unsafe(ffi)` expressions. The Rust provider and interpreter cover the
live set, and the final boolean apply status remains the sole transaction
admission result. The exported builder remains unsafe until rollback, unwind,
and provider identity are proved. No call, allocation, copy, loop, lookup,
lock, hash, or signature operation was added. Exact native codegen signatures,
artifact-bound admission, and verification receipts remain open; the focused
static ratchet therefore deliberately reports this family as unsafe and
unverified.

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

Checkpoint: `os.crypto.ecdsa_p256`, TLS, SSH, JWT, and COSE now propagate the
checked P-256 `Result`; no production path converts bridge/provider failure to
empty bytes or `false`. The provider call count and allocation/copy behavior
are unchanged. Static checks and all six production source checks pass; the TLS
unit-variant parser blocker was replaced by a total match. Census remains
12,023 `rt_*` rows / 3,172 symbols, 1,190 tagged, 638
contract-declared, 10,567 untouched, and zero signed/admitted.

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

## Privileged CPU direct-instruction tranche

- [x] Remove 63 providerless ARM32/ARM64/RV32 `rt_*` declarations from the
  target CPU owners.
- [x] Preserve the public HAL surface while lowering each primitive to one
  direct target instruction and one minimal `inline_asm` authority region.
- [x] Replace the split ARM32 MPIDR read with one architectural MRC operation.
- [x] Encode ARM64 DAIF set/clear using constant architectural immediates.
- [x] Add a static ratchet for declaration absence, exact instruction count,
  capability confinement, and hot-path allocation/lookup/dispatch exclusion.
- [ ] Execute cross-target compiler/assembler checks when an admitted current
  self-hosted toolchain is available.
- [ ] Prove privilege-level preconditions and bind compiler/hardware evidence
  to a signed artifact before any verified/critical promotion.

This tranche improves the hot path by deleting unresolved foreign calls. It
does not label inline assembly safe or verified.

### RV64 follow-up

- [x] Remove ten CPU SFFI declarations and their duplicate freestanding C
  switch/provider implementation.
- [x] Specialize the twelve CSR reads, six writes, four set/clear operations,
  two targeted fences, and four register moves to direct named instructions.
- [x] Preserve explicit memory clobbers for translation and interrupt ordering.
- [ ] Execute cross-target assembly and QEMU evidence on an admitted toolchain.

## Architecture context and timer tranche

- [x] Classify nine context save/restore/switch declarations as raw pointer and
  FFI authority; confine all calls and make the wrapper obligation visible.
- [x] Align initial stacks once at construction and reject RV32 architecture
  mismatch instead of returning successfully.
- [x] Record the unresolved by-value source-context persistence bug across all
  architecture context implementations.
- [x] Remove thirteen ARM timer declarations and 22 fabricated example
  definitions; replace them with ten direct target instructions.
- [x] Make ARM32 CNTPCT one coherent two-output MRRC observation.
- [ ] Redesign context transfer around stable scheduler-owned mutable/borrowed
  contexts and an exact non-returning, artifact-admitted assembly ABI.
- [ ] Execute cross-target assembly, QEMU context-resume, and timer monotonicity
  evidence on an admitted current-source compiler.

## User-entry and VirtIO input tranche

- [x] Tag six ARM32/ARM64 privilege-transfer declarations and all dependent
  wrappers; confine raw calls without changing status or call counts.
- [x] Tag fourteen ARM64/RV64 VirtIO input declarations and four wrappers.
- [x] Reject non-`1` poll status before projecting a fabricated event.
- [x] Record the split global snapshot and missing error-channel blocker.
- [ ] Replace six-call event reconstruction with one fixed-layout stack
  status/out contract and typed `Result<Option<Event>, SffiError>` lift.
- [ ] Bind target providers and non-returning privilege-transfer assembly to
  exact ABI/artifact hashes and signed admission evidence.

## SBI and ARM32 boot-topology tranche

- [x] Tag the providerless RV32 tuple call, both RV64 ecall declarations, the
  RV64 CLINT write, and both ARM32 split-DTB reads as raw FFI authority.
- [x] Confine each raw call lexically without adding wrapper allocation,
  registry lookup, hashing, signing, locks, retries, or generic dispatch.
- [x] Require SBI success before converting extension-probe payloads to bool.
- [x] Pass a live stack-word address to legacy SBI IPI and honor the absolute
  hart-mask base in the CLINT fallback.
- [x] Stop CLINT scanning when the remaining mask is zero and reject hart IDs
  that cannot fit the canonical 32-bit MMIO owner.
- [ ] Replace or implement the providerless RV32 tuple boundary with an exact
  target ABI, then bind it to the loaded artifact and registry identity.
- [ ] Bind RV64 SBI return layout, compiler, firmware, and provider bytes to
  signed evidence before verified or critical promotion.
- [ ] Replace the ARM32 split address calls with one coherent typed boot
  descriptor when its freestanding ABI is available.
- [ ] Run cross-target compiler, OpenSBI/QEMU, firmware-error sabotage, and
  timing/RSS evidence once the admitted current-source toolchain is available.

## RISC-V cache-maintenance tranche

- [x] Tag eight CMO declarations and confine their raw calls to minimal lexical
  FFI scopes.
- [x] Replace linear count-only loops with O(1), zero-stride-safe, saturating
  ceiling division.
- [x] Reject RV32/RV64 address-range overflow before issuing cache maintenance.
- [x] Preserve one direct foreign instruction leaf per covered cache line and
  exclude allocation, lookup, locking, hashing, signing, and retry work.
- [x] Record that RV32 currently imports an RV64-only provider family.
- [ ] Split the target instruction leaf by XLEN or provide a distinct exact RV32
  ABI, without moving cache policy out of Pure Simple.
- [ ] Admit capability probes and exact provider/compiler/artifact identities
  before safe or critical promotion.
- [ ] Retain cross-target assembler, OpenSBI/QEMU, illegal-instruction sabotage,
  latency, code-size, and compiler/emulator RSS evidence.

## Canonical bare-metal MMIO tranche

- [x] Collapse 15 duplicate noalloc declarations into six canonical raw MMIO
  identities.
- [x] Tag each canonical leaf `unsafe(ffi, raw_ptr)` and confine the raw call.
- [x] Export inline wrappers so interrupt, allocator, syscall, and SBI paths add
  no dispatch or allocation layer.
- [x] Add a ratchet for declaration uniqueness, consumer bypass absence,
  lexical authority, and hot-leaf performance shape.
- [x] Reject negative, null, host-width-invalid, and misaligned addresses before
  Rust interpreter volatile access; retain a real aligned read/write test.
- [ ] Introduce typed, target-owned MMIO regions carrying width, alignment,
  ordering, and device authority without per-access dynamic checks.
- [ ] Bind native/interpreter ABI parity and exact loaded provider artifacts to
  signed evidence before verified/critical promotion.
- [ ] Retain cross-target volatile-access sabotage, code-shape, latency, and
  compiler/emulator RSS evidence.

## Volatile MMIO authority tranche

- [x] Tag the thirteen production/freestanding OS volatile, fence, and ARM
  cache declarations with explicit `ffi`/`raw_ptr` authority.
- [x] Confine all OS raw calls and the semihost UART's three volatile calls to
  minimal lexical unsafe blocks.
- [x] Inline the ordinary OS MMIO wrappers and entry-closure aliases; route each
  alias through its owner wrapper so call count remains one.
- [x] Reject null, negative, host-width-invalid, and misaligned volatile
  addresses in the hosted Rust interpreter before dereference.
- [x] Add a focused source ratchet for tags, lexical calls, inline hot wrappers,
  checked Rust lifts, and absence of admission/allocation work.
- [ ] Repair unrelated Rust runtime export and whole-file formatting drift, then
  execute the focused volatile sabotage unit test and formatting gate.
- [ ] Establish target-owned MMIO ranges, exact ABI parity, signed provider
  admission, cross-target code shape, latency, and peak RSS evidence.

## Checked dynload and typed boolean tranche

- [x] Restore checked status/out load, library-symbol, and current-process
  symbol providers across C, Rust runtime, interpreter, dispatch, and codegen.
- [x] Reject interpreter interior-NUL names, null handles, missing symbols, and
  unsupported platforms as errors rather than integer zero.
- [x] Stop coercing `Value::Bool` into the untyped integer call ABI.
- [x] Add typed allocation-free `bool()` and `bool(i64)` status/out thunks and
  preserve false separately from bridge failure.
- [x] Restore and sabotage-test the sealed Linux exact-artifact snapshot loader.
- [x] Extend the C harness to cover legitimate integer zero and typed boolean
  true/false/null-function/null-output outcomes.
- [ ] Replace the checked integer bridge's per-call `[status, value]` allocation
  with a scalar status/out ABI while retaining the public `Result<i64, text>`.
- [ ] Unblock Rust workspace exports and execute Rust/interpreter unit tests.
- [ ] Bind admitted exact artifact and ABI registry to verified signatures;
  current signed-admitted count remains zero.
## 2026-08-26 TCP/UDP ABI closure checkpoint

- [x] Align C, Rust, Simple, and Cranelift TCP/UDP scalar status values on the
  boolean/I8 ABI.
- [x] Preserve negative descriptor/count sentinels and nullable owned read/
  address returns; eliminate unsupported-platform fabricated zero values.
- [x] Implement the C connect-timeout budget with nonblocking connect, poll,
  `SO_ERROR`, and flag restoration.
- [x] Reject invalid TCP family tags in C, Rust, and interpreter lanes.
- [x] Keep successful read allocation count unchanged and add only failure-path
  release; retain direct O(1) status leaves without lookup or dispatch.
- [x] Deduplicate the production `rt_env_cwd` raw declaration through the
  canonical `io_runtime` owner.
- [x] Enforce checked ECDSA ownership in `src/lib/common/crypto/ecdsa_p256.spl`
  through the canonical safe facade without duplicating raw externs.
- [x] Remove the unused raw RSA verifier declaration from the SSH session
  facade; no raw Ed25519 verifier declaration was present there.
- [ ] Admit exact provider artifacts through verified signature jobs; current
  repository-wide signed-admitted count remains zero.

Evidence: focused C syntax PASS with `_GNU_SOURCE`; UDP, TCP consumer, and
network authority audits PASS; Simple owner check PASS; optimizer reports only
generic low-confidence MIR opportunities.  The full C compilation guard is
still blocked by the existing Linux seal-macro bug and a separate process
runtime arity defect.  Do not promote this checkpoint to whole-runtime PASS.

### Checked-crypto owner follow-up

- [x] Keep raw checked ECDSA declarations solely in
  `std.nogc_sync_mut.io.signature_sffi`.
- [x] Require the common P-256 module to import typed `Result` wrappers and
  reject any raw checked or legacy ECDSA redeclaration there.
- [x] Make the global null/signature guard pass without widening unsafe scope.
- [ ] Supply real `SFFI_ADMISSION_JOBS` inputs for exact crypto provider
  artifacts; passing source guards are not signed admission.

### Providerless async ABI removal

- [x] Remove the unused 19-declaration generic async SFFI module after proving
  it has no provider and no consumers.
- [x] Remove native zero-return stub permissions for `future_alloc_ready`,
  `future_map`, and `future_then`.
- [x] Retain Future, Promise, and AsyncIO in their canonical pure-Simple owners.
- [x] Add an executable authority audit preventing the providerless ABI and
  fabricated stubs from returning.
- [x] Check the three canonical owners and run the existing async basics spec
  once (25/25 pass).
- [ ] Continue census-led unsafe minimization; this removal does not supply a
  signed provider admission job.

### Generic interpreter FFI removal

- [x] Prove the all-`u64` dispatcher and compiled-module loader helpers have no
  repository consumers.
- [x] Delete the 14-declaration generic extern module and its two private bridge
  helpers instead of widening unsafe scope.
- [x] Remove the unused loader facade from the interpreter FFI package exports.
- [x] Add an executable guard that retains the typed native registry and rejects
  restoration of `call_ffi_N`, nil-to-zero marshalling, or the removed facade.
- [x] Run the guard, package initializer check, and optimizer once.
- [x] Record the pre-existing legacy-syntax blocker preventing a clean direct
  check of the surviving bridge.
- [x] Attempt lint once and bind its unresolved
  `Linter.lint_source_for_parsed_append` failure to the existing lint-subsystem
  clobber bug; do not report lint as passing.
- [ ] Continue with real provider families and exact-artifact admission; this
  dead-lane removal is not signed verification.

### Providerless QUIC ABI removal

- [x] Confirm `quic_provider_check()` is hard-disabled and no C/Rust quiche
  provider exists.
- [x] Remove the 14 production and 28 mirrored-test raw `rt_quic_*`
  declarations.
- [x] Preserve the public connection API as a pure-Simple terminal-state facade
  with no native handle dispatch.
- [x] Add an authority guard requiring the unadmitted ABI to stay absent.
- [x] Run the guard, source check, compatibility spec, and optimizer once.
- [ ] Introduce native QUIC only through a typed status/out ownership contract
  after authenticated QUIC-TLS and exact-artifact admission are available.

### Dead executable-memory generator spec

- [x] Prove all 16 proposed symbols have no provider, generated target,
  consumer, or live test.
- [x] Delete the unimplemented RWX/raw-function-pointer spec instead of tagging
  it as if an ABI existed.
- [x] Preserve the canonical loader W^X and Rust `ExecutableMemory` owners.
- [x] Add and run an authority audit for dead-symbol absence and RW→RX ownership.
- [x] Remove all 16 stale rows from the seed, interpreter-gap, unbacked, and
  raw-unsafe ledgers; focused interpreter-gap scan passes.
- [ ] Continue auditing the live `rt_mmap*` loader boundary separately; deleting
  this dead parallel design does not verify or sign that provider.

### Live executable-memory provider boundary

- [x] Confirm both Simple owners allocate RW and transition explicitly to RX.
- [x] Reject WRITE+EXEC in Unix and Windows mmap/mprotect providers.
- [x] Reject WRITE+EXEC in the core-C bootstrap and Rust interpreter providers.
- [x] Remove the Windows `PAGE_EXECUTE_READWRITE` translation.
- [x] Add sabotage coverage for direct RWX allocation and RW-to-RWX transition.
- [x] Repair and pass the provider contract audit across all four lanes.
- [x] Pass Unix and GNU core-C syntax checks.
- [ ] Execute the focused Rust sabotage test after unrelated compiler workspace
  export/import drift is repaired; the test is authored but compilation blocks
  before reaching it.
- [x] Synchronize native Unix/Windows/core-C RX transitions without a new SFFI
  symbol, lookup, allocation, copy, or Simple dispatch.
- [x] Fail closed before execute permission in the Rust interpreter on non-x86
  hosts until that lane has a verified cache-sync primitive.
- [ ] Add a verified Rust interpreter cache-sync primitive to enable, rather
  than reject, hosted ARM/RISC-V executable transitions.
- [ ] Bind exact runtime/compiler artifacts and ABI registry to a verified
  signature admission job; signed-admitted count remains zero.

### Signed-admission receipt join

- [x] Repair the verifier output to canonical `simple.sffi-admission.v1`.
- [x] Bind provider, target, signer, artifact, ABI, manifest, report, and symbol
  signatures in the emitted receipt.
- [x] Exercise a freshly verified receipt through `SFFI_ADMISSION_JOBS` and the
  exact provider/signature inventory join.
- [x] Retain all signature, hash, canonicalization, trust, and failed-report
  sabotage controls.
- [ ] Provision an external production trust policy and exact runtime evidence
  inputs; fixture-generated keys must never promote production census rows.

### Providerless debug command output

- [x] Confirm all four `rt_command_output` declarations are genuinely missing
  across C, Rust, interpreter, and native backing.
- [x] Replace the raw text-only boundary with one canonical bounded
  `process_run_bounded` owner returning `Result<text, text>`.
- [x] Propagate nonzero exit and stderr through typed errors instead of empty
  successful output.
- [x] Cap each command at 120 seconds and 1 MiB without adding a second child,
  retry, per-byte loop, registry lookup, or generic dispatch.
- [x] Pass external values as argv or fixed-script positional parameters so
  shell metacharacters remain data rather than executable syntax.
- [x] Add real success/failure coverage and an authority audit preventing the
  providerless symbol from returning.
- [x] Pass source checks, the 3/3 compatibility spec, authority guard,
  direct-runtime guard, and optimizer analysis once.
- [x] Attempt lint once and retain the existing
  `Linter.lint_source_for_parsed_append` blocker rather than claiming PASS.
- [ ] Verify the same spec with an admitted current-source pure-Simple Stage-4
  runtime; bootstrap-seed execution is compatibility evidence only.
- [ ] Bind the canonical process provider to exact signed admission evidence;
  repository-wide signed admission remains zero.

### Unimplemented interpreter debug hooks

- [x] Inventory the 14 `rt_hook_*` identities across the three DAP/generator
  declaration surfaces; none has an observed provider.
- [x] Mark all 42 raw declarations `unsafe(ffi)` and add a focused authority
  guard that rejects missing annotations or missing capability-gap wiring.
- [x] Route unresolved `rt_hook_*` symbols through the typed interpreter
  capability-gap family and cover it with the targeted Rust unit suite (3/3).
- [x] Confirm the focused census: 42/42 rows and 14/14 symbols are explicitly
  unsafe-tagged; signed admission remains zero.
- [ ] Implement a versioned typed debug-hook provider or remove each raw API;
  current annotations do not prove null/ownership safety or provider admission.
- [ ] Execute the capability-gap fixture using a current admitted Simple runtime;
  the installed compatibility runner predates this Rust dispatch.

### Owned SimpleOS C-provider census coverage

- [x] Scan both `src/runtime` and `src/os` owned C/C++ trees when identifying
  source-backed foreign providers; retain vendor exclusions.
- [x] Reclassify 68 symbols (including PCI, network, and raw memory helpers)
  from false missing states to `c_runtime_source_only`.
- [x] Remove the 60 correspondingly stale entries from the frozen unbacked
  baseline; this is a reviewed classification correction, not admission.
- [ ] Reconcile the global unbacked ratchet's unrelated 46 new / 370 stale
  entries without regenerating its baseline blindly.
- [ ] Bind each source-backed provider to exact ABI, artifact, and signature
  evidence before treating it as safe or critical-admissible.

### HDA PCI boundary

- [x] Classify all four HDA PCI scalar externs as `unsafe(ffi)` and contain
  every call in a tiny `@always_inline` lexical owner.
- [x] Add source authority coverage proving four declarations/four owners and
  no direct raw HDA PCI call outside those owners.
- [x] Preserve boot-path complexity and memory behavior; do not substitute the
  allocating full-bus `PciBus` owner for this scalar target ABI.
- [ ] Define one versioned target PCI contract (especially BAR/IRQ field
  numbering), add real x86_64 provider code, and bind it to an artifact.
- [ ] Run the existing native-stub spec under a current admitted runtime; the
  bootstrap runner lacks its test-only provider.

### Debug ptrace/DWARF owner consolidation

- [x] Remove the 46 duplicate raw ptrace/DWARF declarations from four debug
  frontend/mirror modules and import the canonical `std.sffi.debug` owner.
- [x] Add an authority audit that keeps the eight ptrace declarations annotated
  at the owner and rejects their reintroduction in the four consumer modules.
- [x] Preserve hot-path behavior: the change is declaration elimination only,
  with no wrapper call, allocation, copy, lookup, or dynamic dispatch.
- [ ] Replace raw ptrace arrays/register maps and DWARF text/array returns with
  typed owned/status contracts, then admit an exact signed provider artifact.

### Providerless legacy CUDA session

- [x] Confirm the legacy engine2d CUDA-session façade has no production import
  and nine providerless/conflicting raw declarations.
- [x] Remove its execution façade instead of synthesizing scalar/text results;
  preserve only the pure bounded cache bookkeeping used by its real contract.
- [x] Pass the same 2/2 cache spec, source check, optimizer analysis, and a
  guard that rejects raw CUDA externs/calls returning to that module.
- [ ] Migrate any future engine2d CUDA execution through the existing typed
  CUDA owner with versioned ABI/evidence admission, never this cache module.

### Serial raw-owner consolidation

- [x] Delete the unused app-level serial raw declaration copy and retain one
  canonical no-GC serial owner.
- [x] Mark all seven retained raw serial declarations `unsafe(ffi)` and route
  dedicated-hardware transport through its typed `SerialPort` façade.
- [x] Remove the providerless availability call by returning a typed error;
  add an authority guard and a no-hardware fail-closed unit spec.
- [x] Fix default-stdout inventory spooling so full census aggregation cannot
  read from its own stdout pipe.
- [ ] Define a versioned serial status/out ABI, validate text/handle ownership,
  and bind C/Rust provider artifacts to signed admission evidence.

### WebGPU raw-owner consolidation

- [x] Remove the unused duplicate `webgpu_ffi` owner and the no-import,
  providerless `WebGpuSession` execution façade.
- [x] Preserve only pure bounded shader-cache bookkeeping and add an authority
  audit that rejects reintroduced raw calls/declarations.
- [x] Mark the eleven still-active `webgpu_sffi` declarations `unsafe(ffi)`
  without adding rendering-loop work, copies, or dispatch.
- [ ] Replace active WebGPU bool/handle/text contracts with versioned typed
  status/out contracts and admit the exact C/Rust provider artifact.

### Providerless legacy Metal session

- [x] Confirm the no-GC engine2d Metal-session façade has no production import
  and ten providerless raw declarations.
- [x] Remove its execution façade and preserve only the fixed pure pipeline
  cache/rejection bookkeeping used by its real contract.
- [x] Pass the existing 2/2 cache spec, source check, optimizer analysis, and
  a guard that rejects raw Metal declarations/calls returning to this module.
- [ ] Migrate any future engine2d Metal compute execution through an admitted
  typed owner with versioned ABI and artifact/signature evidence; do not revive
  this cache module as an execution boundary.

### Intel Engine2D raw-owner consolidation

- [x] Remove the eleven raw `rt_intel_engine2d_*` declarations from the active
  GC backend and import the canonical no-GC wrapper functions instead.
- [x] Mark all 21 declarations in each remaining Intel raw-owner surface as
  `unsafe(ffi)` and add an authority audit covering 42 raw rows.
- [x] Preserve existing backend helper names and one-call render-path shape;
  run focused source checks, existing fallback spec, and optimizer analysis.
- [ ] Replace both legacy Intel owners with one versioned typed Level Zero ABI;
  then validate pointer/array layouts and admit a signed exact provider.

### OpenCL raw-owner classification

- [x] Confirm that `sffi_opencl` is the one raw OpenCL declaration owner and
  that the owned C implementation is source evidence only.
- [x] Mark all 20 raw OpenCL declarations `unsafe(ffi)` and add an authority
  guard rejecting duplicate owners.
- [x] Run the existing eight-case fail-closed OpenCL spec, source check, and
  optimizer analysis without altering the dispatch path.
- [ ] Define typed span/handle/status contracts, bind the C provider to an
  exact artifact, and require signature/evidence admission before safe use.

### ROCm Engine2D raw-boundary classification

- [x] Inventory the canonical ROCm I/O owner and the two legacy Engine2D raw
  owners; retain active compatibility behavior rather than deleting it blindly.
- [x] Mark all 25 legacy Engine2D raw declarations `unsafe(ffi)` and add a
  regression audit for their two declaration counts.
- [x] Run source checks, the existing 13-case ROCm spec, and optimizer analysis
  without changing any GPU call path.
- [ ] Replace legacy dispatch façades with one typed ROCm ABI, validate array/
  handle ownership and status semantics, and admit an exact signed provider.

### 3D GPU raw-owner deduplication

- [x] Convert the four duplicate `ffi_*3d` raw modules into API-preserving
  compatibility re-exports of their canonical `sffi_*3d` owners.
- [x] Mark the twelve remaining CUDA/ROCm/Intel/Vulkan 3D raw declarations
  `unsafe(ffi)` and add a four-owner authority guard.
- [x] Source-check all canonical and compatibility modules; run optimizer
  analysis on every canonical owner without changing runtime dispatch.
- [ ] Replace the providerless/legacy 3D ABI names with versioned typed
  contracts and exact signed provider admission.

### OpenGL raw-boundary classification

- [x] Mark all nineteen raw OpenGL declarations `unsafe(ffi)` in the sole
  no-GC owner and make each direct wrapper call lexical-unsafe.
- [x] Preserve boolean operation results and change only nullable provider
  error text to `text?`, preventing a null message from claiming non-null text.
- [x] Add a single-owner authority audit; run source checks, the existing
  fallback spec, and optimizer analysis without adding render-path work.
- [ ] Replace legacy OpenGL handles/buffers with versioned typed contracts,
  prove buffer extent/ownership, and admit an exact signed provider artifact.

### File-operations raw-boundary classification

- [x] Mark all nineteen raw file-operation/mmap declarations `unsafe(ffi)`;
  apply `raw_ptr` only to raw mapping address/extent operations.
- [x] Make every direct raw call lexical-unsafe without changing public API,
  operation count, retry behavior, allocation, copy, lookup, or dispatch.
- [x] Add a raw-owner annotation guard and record the stale bootstrap-artifact/
  test blockers instead of accepting a fabricated fallback.
- [ ] Replace legacy mmap/hash non-null text and raw integer mapping handles
  with typed nullable/status/owned-resource contracts; register each contract
  in every execution lane and require signed provider admission.

## Acceptance

Runnable oracles for the remaining open boxes: `test/03_system/plan_acceptance/sffi_universal_admission_next_spec.spl`
(tagged `@tag:in-development`; one `it` per open box — see
`doc/03_plan/agent_tasks/plan_remains_acceptance_2026-09-05.md`).
