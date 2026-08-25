<!-- codex-research -->
# SFFI universal admission: next local research checkpoint

**Date:** 2026-08-25  
**Tree:** `fbde06072d5`
**Scope:** owned `src/compiler`, `src/compiler_rust`, `src/lib`, `src/os`, and
SFFI audit tooling; vendor trees excluded.

## Verdict

Simple SFFI is **not globally safe, verified, or signed**. The repository has
useful fail-closed pieces, but no current evidence proves universal production
admission across interpreter, JIT, native, dynload, and SimpleOS.

Do not reuse the 2026-08-23 totals as current-tree statistics. They use an older
scanner and generous file-level unsafe attribution. Newer declaration and call
totals are also historical checkpoints with different units. The source call
census remains a lower bound until resolved-HIR inventory covers aliases,
re-exports, generated calls, methods, and indirect callables.

## Fresh source-ledger census

The repository-owned census tools were run once on this tree. These are
source-ledger measurements, not resolved-HIR ABI proof:

| Unit | Total | Unsafe tagged | Signed/admitted | Untouched |
| --- | ---: | ---: | ---: | ---: |
| `rt_*` declaration rows | 12,128 | 951 | 0 | 10,907 |
| distinct `rt_*` symbols | 3,173 | 695 | 0 | 2,246 |

Distinct `rt_*` provider-language provenance is 1,321 linked-native symbols
whose implementation language is unknown, 1,012 with no provider observed,
591 Rust symbols, and 249 C/C++ symbols.

The separate raw-call authority census found 21,757 call sites across 3,131
caller files and 3,297 called symbols. Only 1,754 sites were inside lexical
`unsafe(ffi)` and 509 inside function-level FFI authority; 19,494 lacked
explicit authority. Its ratchet failed (`19,494 > 19,412`). This scanner is a
bounded source heuristic and explicitly does not resolve aliases, re-exports,
or generated declarations; resolved HIR remains the required final authority.

### 2026-08-25 post-admission refresh

After the exact-artifact signature and typed-boolean work landed, the full
repository-owned inventory was rerun once. The distinct `rt_*` symbol total and
provider-language split were unchanged, while declaration tagging advanced:

| Unit | Total | Unsafe tagged | Signed/admitted | Untouched |
| --- | ---: | ---: | ---: | ---: |
| `rt_*` declaration rows | 12,131 | 958 | 0 | 10,901 |
| distinct `rt_*` symbols | 3,173 | 696 | 0 | 2,246 |

Distinct provider-language provenance remains 1,321 linked-native/unknown,
1,012 with no provider observed, 591 Rust, and 249 C/C++. This proves that the
tree is still not universally admitted. It also exposed 26 duplicate Simple
`rt_mkdir_p` declarations whose legacy C and canonical pointer/length provider
shapes were not one authoritative ABI. The follow-up consolidation removed all
Simple declarations and routes callers through `std.io_runtime.mkdir_p` and
its already-scoped `rt_dir_create_all` owner. The focused lint now rejects any
reintroduction. This changes neither asymptotic work nor allocation count; it
removes a duplicate boundary and an unconditional LLVM declaration.

After the subsequent sleep and current-directory consolidations, one final
full inventory run for this checkpoint reported:

| Unit | Total | Unsafe tagged | Signed/admitted | Untouched |
| --- | ---: | ---: | ---: | ---: |
| `rt_*` declaration rows | 12,070 | 963 | 0 | 10,835 |
| distinct `rt_*` symbols | 3,171 | 697 | 0 | 2,243 |

The distinct provider split is now 1,319 linked-native/unknown, 1,012 with no
provider observed, 591 Rust, and 249 C/C++. `rt_sleep_ms` no longer has a raw
Simple declaration: callers use the existing scoped `rt_thread_sleep` owner.
`rt_env_cwd` now has one hosted declaration with the truthful `text?` contract;
the total wrapper maps provider failure to `"."` and replaces the former
`pwd` subprocess. The four bootstrap-library mirrors also declare `text?` and
place calls inside lexical `unsafe(ffi)` scopes. Zero production symbols are
cryptographically admitted, so global safety and verification remain false.

### TCP descriptor/read contract checkpoint

The canonical TCP module had ambient raw calls and an impossible safety check:
`rt_io_tcp_read` returned `[u8]`, providers converted both read failure and EOF
to `[]`, and `TcpStream.read` tested `data.len() < 0`. The repaired contract is
`[u8]?`: `nil` is invalid input/provider/read failure, while `[]` is a valid
zero-length request or EOF. C, Rust runtime, and interpreter now agree, and the
Windows C fallback returns the runtime nil value rather than integer zero for
TCP text/address objects. All 20 Simple declarations use the optional contract
and every direct call is inside a one-expression `unsafe(ffi)` scope.

The source ledger after this tranche reports 12,070 `rt_*` declaration rows,
1,005 unsafe-tagged rows, 10,796 untouched rows, 3,171 distinct symbols, 720
unsafe-tagged symbols, 2,228 untouched symbols, and zero admitted production
symbols. Provider language counts remain those of the immediately preceding
full census because this tranche changes contracts, not provider ownership.

Successful TCP reads retain one provider call and the existing buffer work.
The only hot-path addition is the required predictable nil check; there is no
hash, lookup, lock, subprocess, generic dispatch, or new allocation. Focused
Rust runtime and interpreter tests each passed once, and the C runtime compile
gate compiled 118 files with zero errors (two dependency-gated skips). The
self-hosted Simple/optimizer/cross-lane gates remain unavailable and are not
claimed.

## Current enforcement boundary

- Normal and bootstrap MIR lowering now reject non-unit fallthrough with
  `E-SFFI-016`; the bootstrap change remains behaviorally unverified.
- Typed HIR identifies direct named extern calls and the safety checker finds
  calls outside lexical `unsafe(ffi)`. Default driver severity remains advisory;
  only Critical/Verified deny.
- `raw_sffi_call` remains `allow` in the default lint profile. The declaration
  and call-site ratchets freeze debt but do not verify contracts.
- The audit-only HIR inventory carries no artifact/signature evidence and cannot
  establish production admission.

## Current dynamic-provider boundary

- `ExactArtifactDynLib` provides a Linux immutable snapshot and exact digest.
- `SffiAdmissionReceiptV1` parses bounded canonical text but performs no
  cryptography and is source-forgeable.
- Evidence-bound identity checking compares provider, target, artifact, ABI
  registry, and source-signature closure, then atomically resolves cached i64
  slots. It has no production caller and does not validate loader authority.
- The standalone evidence-admission audit verifies Ed25519 trust, exact inputs,
  ABI closure, artifact symbols, and verification receipts. No compiler/runtime
  loader invokes it.
- Rust `NativeLibManager` and raw `spl_dlopen` load providers without that
  evidence gate. Production Simple callers likewise bypass manifests.
- `FfiManifest.validate_library` checks only symbol presence; it does not prove
  ABI, nullability, ownership, or signing. Its stronger cached resolvers are
  currently unused.

## Ownership and memory findings

`std.sffi.dynamic` is the canonical no-GC synchronous owner and compatibility
modules should export it. `ffi/dynamic_versioned.spl` duplicates the canonical
implementation instead of acting as a facade. `MultiVersionLoader` and
`DynLoader` retain process-global maps without eviction, so provider handles and
path text can remain live indefinitely.

Legacy dynamic calls perform per-call symbol lookup; checked integer transport
also allocates a two-element result array. Cached resolved slots remove repeated
lookup, but remain an unsafe migration ABI restricted to `i64(i64...)`.

## Performance invariant

Admission must be one-time:

```text
immutable artifact snapshot -> hash/signature/trust/ABI/receipt checks
    -> resolve complete symbol closure -> atomically publish cached typed slots
```

No admitted hot call may add hashing, signature verification, filesystem work,
path search, string lookup, dictionary lookup, generic decoding, mutex traffic,
or allocation. Required status/null/descriptor checks remain enabled.

## Statistics contract

Every future count must record tree ID, scanner identity, executable identity,
timestamp, exclusions, and exact unit. Keep these units separate:

- declarations;
- distinct symbols;
- live call sites;
- provider modules/families;
- freshly reverified cryptographic admissions.

States are mutually exclusive per row: `admitted_artifact_bound`,
`unsafe_contract_declared`, `unsafe_or_contract_missing`, and
`unknown_uninventoried`. Backed symbols, source claims, saved receipts, fixture
passes, and immutable snapshots are not “verified” or “signed.”

## Research coordination

Read-only sidecars covered compiler enforcement, library/dynload ownership, and
documentation/evidence consistency. `/root` merged and reviewed the findings.
The source-ledger censuses above were run once. The canonical release path
identified itself as the Rust bootstrap seed and the focused baseline spec
failed before execution with the already-recorded `function unsafe not found`
defect (`0.79 s`, `190,448 KiB` peak RSS). Repository policy forbids treating
that seed as self-hosted correctness or optimizer evidence, so the criterion was
not rerun and the implementation slice remains unverified.

## TCP listener checkpoint

Raw `rt_io_tcp_bind`, `rt_io_tcp_accept`, and `rt_io_tcp_accept_timeout`
declarations now state their descriptor/sentinel contracts and their direct
owned callers use one-expression `unsafe(ffi)` scopes. The timeout ABI still
conflates timeout and provider failure, so it remains explicitly unsafe rather
than being promoted to a safe typed contract. The change preserves one direct
call, the existing sentinel branch, and the existing allocation shape per site.

The post-TCP census reports 12,070 declaration rows and 3,171 distinct declared
symbols. Of those rows, 1,057 are unsafe-tagged, 754 have documented contracts,
485 are unsafe-minimized, and 10,744 remain untouched. Provider definitions are
2,378 C, 2,178 Rust, 576 Simple, and 219 C++. Cryptographically verified,
signed, and admitted rows remain zero; annotations are not admission evidence.

## TCP boolean and timeout ABI checkpoint

The TCP close, flush, shutdown, bind/listen status, and socket-option families
now use semantic `bool` in C and Rust providers and the backend boolean carrier
(`I8`) in native codegen. Timeout setters no longer reuse an incompatible
tagged `RuntimeValue`/raw-integer symbol: their raw ABI is `(i64 fd, i64 ms) ->
bool`, with non-positive milliseconds clearing the timeout. Safe Simple
wrappers retain `i64?` and lower `nil` to `-1` once before the direct call.
This removes runtime-value decoding and uses saturating millisecond-to-nanosecond
conversion; it adds no lookup, allocation, lock, or generic dispatch.

The refreshed ledger remains 12,070 rows / 3,171 symbols. Unsafe-tagged rows
increased to 1,148 and untouched rows decreased to 10,653. Contract-documented
rows remain 754 and unsafe-minimized rows remain 485 because source annotations
alone are not executable admission contracts. Verified-and-signed rows remain
zero.

## Executable reason-contract census checkpoint

The inventory now recognizes explicit unsafe reason clauses such as `false
means close failed`, `negative ... means failure`, nil/empty distinctions, and
socket-family mappings as documented contracts. This changes only debt
classification: it does not create evidence, verify a signature, or admit an
artifact. A unit fixture proves a false-status reason is documented while its
cryptographic admission and evidence remain absent.

After TCP connect/accept/family hardening and removal of the dormant fabricated
C bind provider, the ledger is 12,070 rows / 3,171 symbols: 1,163 unsafe-tagged,
883 contract-documented, 614 unsafe-minimized, and 10,638 untouched. Provider
definitions are C 2,377, Rust 2,178, Simple 576, and C++ 219. Verified-and-signed
remains zero.

## Bootstrap shell raw-contract checkpoint

All 25 filesystem, environment, process, path, search, and directory externs in
the bootstrap shell module now carry adjacent operation-specific `unsafe(ffi)`
metadata. Contracts identify ambiguous empty file/path/list values, recursive
filesystem effects, captured process output and launch failure, target-owned
path text, and process-environment mutation.

`rt_env_get` is now correctly optional and `env.get` applies its default only
to `None`, not to a legitimate empty environment value. This preserves the same
single environment lookup and removes the fabricated equivalence between
missing and empty. No filesystem scan, process launch, output capture,
allocation, copy, environment read, branch beyond the existing default choice,
or generic dispatch was added. A static ratchet fixes all declarations and the
optional lookup contract.

Estimated declaration totals remain 11,651 / 3,137 symbols. Unsafe-tagged rows
increase from 2,154 to 2,178, untouched rows decrease from 9,302 to 9,278, and
exact-artifact verified-and-signed admission remains zero.

## Bootstrap math ABI-conflict checkpoint

The bootstrap core math module declares 24 `rt_math_*` functions with `f32`
parameters/results, but the canonical Rust runtime exports those exact symbol
names with `f64` ABIs. This is an ABI conflict on native lanes, not a numerical
precision preference. Changing the shared provider to `f32` would break the
canonical `f64` API; widening the bootstrap public API would also be an
incompatible workaround.

Every bootstrap declaration now explicitly records the conflict as
`unsafe(ffi)`. A static ratchet fixes both sides while the correct solution is
implemented: generated `_f32` provider symbols and typed direct thunks, with
both signature families in the ABI registry. That solution preserves the
public `f32` API and adds no allocation, boxing, lookup, conversion loop, or
generic dispatch. The current annotation pass changes no math call, branch,
conversion, result, or memory behavior and does not claim verification.

Estimated declaration totals remain 11,651 / 3,137 symbols. Unsafe-tagged rows
increase from 2,178 to 2,202, untouched rows decrease from 9,278 to 9,254, and
exact-artifact verified-and-signed admission remains zero.

## UDP scalar-option ABI checkpoint

The UDP `connect`, `set_broadcast`, `set_read_timeout`, and `set_nonblocking`
family now uses one Simple-facing contract across the C provider, Rust provider,
interpreter registry, and native-codegen registry. Status values are semantic
`bool`; the optional timeout is lowered once by the safe Simple wrapper to an
`i64` millisecond value with `-1` meaning no timeout. Interpreter entry points
reject non-boolean/non-scalar bridge values instead of applying truthiness or a
default. The benchmark caller now stops if nonblocking setup fails rather than
silently running a blocking workload.

The hot path remains constant-time and allocation-free beyond the provider's
existing socket-registry lookup: there is no hashing, signature verification,
symbol/name lookup, generic marshalling, heap allocation, or data copy per
option call. Focused evidence passed: the C translation-unit syntax check, 3
Rust runtime contract tests, 8 compiler interpreter/codegen tests, and the
cross-lane SFFI signature ratchet. The canonical self-hosted optimizer was not
run because the repository still records the admitted Stage-4 runtime as
blocked; the Rust seed was not substituted.

A fresh source-only census reports 12,038 `rt_*` declaration rows and 3,179
distinct `rt_*` symbols. Of the rows, 1,187 are unsafe-tagged, 562 have an
executable reason contract and minimal unsafe scope, 10,581 remain untouched,
and zero are exact-artifact verified-and-signed. Source-only mode deliberately
reports provider language as `none_observed`; the older C/Rust/Simple/C++
provider counts are not reused as if they described this changed revision.

## UDP data-path null/empty and ownership checkpoint

The UDP data path now distinguishes a valid zero-length datagram from provider
failure in every implemented lane. `rt_io_udp_recv` returns `[u8]?` and
`rt_io_udp_recv_from` returns `([u8], text)?`: `nil` means invalid input,
`WouldBlock`, or provider failure, while a present empty array means an actual
zero-length datagram. Send operations return a negative status on invalid input
or provider failure; zero remains the valid length of an empty datagram. Receive
sizes outside `0..65535` fail before allocation or system I/O.

The C and Rust providers allocate one packed runtime byte buffer and receive
directly into it. Every failed receive frees that buffer. Rust peer-address
formatting uses a fixed 64-byte stack buffer and only the required runtime text
allocation; it does not create an intermediate `String`. The benchmark now uses
the connected-shape receive API when it intentionally discards the peer address,
so it avoids tuple/text allocation and correctly counts zero-length datagrams.
A static ratchet rejects payload copies, intermediate collections/strings,
hashing, dynamic lookup, and new registry types in the Rust data wrapper.

Focused evidence passed: C syntax, 5 runtime tests including a real loopback
zero-length datagram, 11 compiler interpreter/codegen tests, mirrored benchmark
parity, and the cross-lane SFFI ratchet. The refreshed source-only ledger is
12,038 `rt_*` declaration rows / 3,179 symbols: 1,200 unsafe-tagged, 568
contract-documented and unsafe-minimized, 10,572 untouched, and zero
exact-artifact verified-and-signed.

## Common ECDSA P-256 checked-result checkpoint

`std.common.crypto.ecdsa_p256` no longer calls the legacy signing and
verification ABIs that collapse bridge failures into an empty signature or
`false`. Signing now returns `Result<[u8], text>` and accepts only a two-field
checked descriptor with status zero and an exactly 64-byte signature.
Verification returns `Result<bool, text>`: a genuine mismatch is `Ok(false)`,
while malformed SPKI/signature shapes, corrupt statuses, and bridge failures
are `Err`. The typed wrapper propagates the result instead of constructing
`Signature.new([])`.

Both common and canonical signature wrappers put each checked raw call in a
one-statement lexical `unsafe(capabilities: [ffi])` scope. No hashing, symbol or
map lookup, input conversion, payload copy, or provider allocation was added.
The focused static guard and two-file source check passed. The executable crypto
spec is blocked before this module by an unrelated parser error in
`src/app/io/env_access_host.spl` (`expected Comma, found Pub`). The available
binary also identifies itself as the Rust bootstrap seed, so it is not accepted
as self-hosted verification.

The refreshed source-only ledger remains 12,038 `rt_*` declaration rows and
3,179 symbols: 1,202 rows are unsafe-tagged, 650 are in
`unsafe_contract_declared`, 10,570 are untouched, and zero are exact-artifact
verified-and-signed.

## P-384/P-521 unresolved-provider removal checkpoint

The four advertised `rt_ecdsa_p{384,521}_{sign,verify}` declarations had no C
or Rust implementation, interpreter registration, or typed codegen entry. They
could therefore only fail resolution or be replaced by a fabricated weak/stub
result. They are now removed from the sync and async signature facades. The SSH
host-key dispatcher returns `Result<bool, text>` and reports that these
algorithms require their canonical pure-Simple providers instead of mapping
provider absence to `false`.

The working P-384/P-521 implementations remain the pure-Simple
`os.crypto.p384` and `os.crypto.ecdsa_p521` engines already used by TLS. This
removal eliminates foreign dispatch and cannot add hot-path hashing, lookup,
allocation, or copying. A static ratchet rejects reintroduction of any of the
four raw declarations and asserts that both pure-Simple sign/verify owners
remain present. The ratchet and focused two-module source check passed; the
available executable still identifies itself as a bootstrap seed and is not
accepted as self-hosted verification.

Removing the nonexistent APIs changes the source-only ledger to 12,034 `rt_*`
declaration rows and 3,175 symbols: 1,198 rows are unsafe-tagged, 646 are in
`unsafe_contract_declared`, 10,570 are untouched, and zero are exact-artifact
verified-and-signed.

## SSH session crypto-authority reduction checkpoint

The SSH session and helper modules declared raw RSA-SHA256 and Ed25519 verify
externs that they never called. Those three declarations are removed. A static
ratchet prevents these session modules from reacquiring direct signature
verification authority; verification belongs to the checked signature owner.
This is a pure surface reduction with no runtime branch, allocation, copy,
lookup, hashing, or dispatch change. The ratchet and focused two-module source
check passed, while the available executable still identifies itself as the
bootstrap seed rather than admitted self-hosted evidence.

The source-only ledger is now 12,031 `rt_*` declaration rows / 3,175 symbols:
1,198 rows unsafe-tagged, 646 `unsafe_contract_declared`, 10,567 untouched, and
zero exact-artifact verified-and-signed.

## Canonical signature facade checked-result checkpoint

The canonical no-GC signature facade no longer declares the eight legacy
RSA-SHA256, RSA-SHA512, Ed25519, and ECDSA-P256 sign/verify entry points. Its
existing public names now return `Result` and delegate to the corresponding
checked provider contracts. A genuine verification mismatch remains
`Ok(false)`; malformed arrays, private keys, signature shapes, corrupt result
descriptors, and provider signing failure are typed errors. Signing can no
longer expose an empty array as a successful value.

Primary compiler, TLS, Ed25519, and cross-provider specs were updated so
positive vectors unwrap checked results and malformed cases assert `Err`.
Production TLS/package consumers already used the checked names. The change
performs the same one cryptographic provider call and adds only bounded status,
descriptor-length, and signature-length checks. It adds no per-call hash beyond
the algorithm itself, symbol lookup, map lookup, generic dispatch, input copy,
or provider allocation.

The static ratchet and facade source check passed. Executable SSpec remains
blocked before the target spec by the unrelated parser error in
`src/app/io/env_access_host.spl`; the available binary also identifies itself
as the bootstrap seed. The source-only ledger is now 12,023 `rt_*` declaration
rows / 3,172 symbols: 1,190 tagged, 638 `unsafe_contract_declared`, 10,567
untouched, and zero exact-artifact verified-and-signed.

## OS ECDSA P-256 result-propagation checkpoint

`os.crypto.ecdsa_p256` no longer imports the deleted raw runtime symbols. Its
fixed-width sign and verify APIs consume the checked facade and return
`Result`. TLS maps provider errors separately from cryptographic mismatch, SSH
and JWT propagate errors, and COSE sign/verify dispatch now carries typed
`CoseError` values rather than returning an empty signature or `false` for an
unavailable/malformed provider result.

The data path still performs exactly one provider cryptographic call. The
change adds only bounded result/status matching and removes sentinel tests; it
adds no lookup, hashing beyond ECDSA itself, payload copy, allocation, or
generic dispatch. The static guard and all six production-module source checks
passed. The TLS verifier's unsupported compact unit-variant pattern was
replaced by an explicit total match, removing that parser blocker. The
available binary remains a bootstrap seed, not admitted self-hosted proof.
Both P-256 spec mirrors are byte-identical; the TLS mirror's pre-existing
placeholder assertions were replaced by the canonical real value/error checks.

No declaration was added or removed in this propagation tranche, so the
source-only ledger remains 12,023 `rt_*` rows / 3,172 symbols: 1,190 tagged,
638 `unsafe_contract_declared`, 10,567 untouched, and zero exact-artifact
verified-and-signed.

## OS RSA typed-result checkpoint

`os.crypto.rsa` no longer redeclares or directly calls the four legacy
RSA SHA-256/SHA-512 sign/verify runtime symbols. It consumes the canonical
checked signature facade, exposes `Result` from signing and verification, and
JWT now propagates provider/malformed-input errors instead of interpreting an
empty signature or verification bridge failure as a cryptographic result.
The mirrored RSA specs assert `Ok(true)`, `Ok(false)`, and typed failures.

The normal automatic signing path still makes exactly one hosted provider call
on success and invokes the Pure Simple fallback only after a typed hosted
failure. Comparison modes retain their intentional two-engine behavior. There
is no new lookup, hash beyond RSA itself, payload copy, generic dispatch, or
success-path error allocation; failure text is allocated only on failure.

The focused static checked-caller ratchet passed. The production source-check
gate refused the only available executable because it identifies as a
non-production bootstrap runtime, so this tranche is not executable-verified
or artifact-admitted. The full census run was stopped after it emitted its
large inventory without converging; the exact declaration delta is four rows
removed and no rows added. Applied to the preceding ledger, the source-only
count is 12,019 `rt_*` declaration rows / 3,172 symbols: 1,190 tagged, 638
`unsafe_contract_declared`, 10,563 untouched, and zero exact-artifact
verified-and-signed.

## Ed25519 seed-signing canonical-owner checkpoint

The optional `rt_ed25519_sign_seed` ABI now has one canonical declaration and
a checked wrapper in `signature_sffi`. The wrapper rejects invalid seed/public
key lengths before dispatch, requires a present 64-byte signature afterward,
and returns typed provider/contract errors. `os.crypto.ed25519` no longer owns
or calls the raw symbol, and its previously inconsistent `ed25519_sign_live`
API now returns `Result` throughout instead of treating a runtime `Result` as
an array or falling back to an empty public result.

The live runtime path retains its existing diagnostic schedule: one direct
seed-sign provider call plus its component-runtime comparison. Normal
Pure-Simple-first and runtime-first selection retain their previous ordering;
no lookup, payload copy, hash beyond Ed25519 itself, generic dispatch, or
success-path error allocation was added. The focused static ratchet passed.
The policy-accepted production runtime remains unavailable, so executable
verification and signed admission remain open.

This change relocates rather than adds/removes the one declaration, so the
ledger remains 12,019 rows / 3,172 symbols, 1,190 tagged, 638
`unsafe_contract_declared`, 10,563 untouched, and zero exact-artifact
verified-and-signed.

## Common P-256 canonical-owner checkpoint

`std.common.crypto.ecdsa_p256` now imports the canonical checked signature
facade instead of redeclaring the P-256 sign and verify providers. Its existing
SPKI-to-raw-point validation and exact 64-byte signature contract remain local.
The shared verification lift now also rejects provider statuses above `1`, so
unknown statuses cannot be converted to `Ok(false)`.

The sign and verify hot paths still make one provider call. The migration adds
no lookup, copy, allocation, hashing beyond ECDSA itself, or generic dispatch;
it removes duplicate unsafe declarations and their local descriptor decoder.
The focused static ratchet passed. Production source checking remains blocked
by the policy-rejected bootstrap executable recorded above, so this is not
artifact admission. The exact declaration delta is two tagged rows removed and
none added: 12,017 rows / 3,172 symbols, 1,188 tagged, 636
`unsafe_contract_declared`, 10,563 untouched, and zero exact-artifact
verified-and-signed.

## General crypto unresolved-provider removal checkpoint

The general crypto facade advertised 17 raw symbols, duplicated again by
`app.io.crypto_ffi`. A provider search across Rust runtime/compiler and C
runtime sources found an implementation only for `rt_random_hex`; the other 16
hash/HMAC/password/AES/key/PBKDF2/random-byte symbols had no implementation.
The app module is now a zero-cost re-export. The canonical facade routes
SHA-256/SHA-512/SHA3-256/BLAKE3 and HMAC-SHA256/SHA512 to existing in-tree
owners, removes the unsupported password/AES/key/PBKDF2 advertisements, and
keeps only `rt_random_hex` under one lexical `unsafe(ffi)` wrapper with
presence, exact-length, lowercase-hex, and nonzero-entropy validation.
The async compatibility facade now exports only this supported surface, so it
cannot keep the removed provider names alive through another module path.

The supported algorithms remain linear in input length. CSPRNG remains one
provider call plus its existing linear output validation. No lookup, retry,
generic dispatch, or extra entropy buffer was added. Hash/HMAC previously had
no callable provider, so routing them to Pure Simple changes an unresolved
operation into a real implementation rather than regressing an executable
baseline. Existing entropy failure specs and crypto vector suites remain the
correctness coverage. The focused static ratchet passed; production execution
is still blocked by the policy-rejected bootstrap runtime.

Thirty-three declaration rows and sixteen unsupported symbol identities are
removed. The source-only ledger is now 11,984 rows / 3,156 symbols: 1,189
tagged, 637 `unsafe_contract_declared`, 10,529 untouched, and zero
exact-artifact verified-and-signed.

## Web session-token entropy-owner checkpoint

`app.ui.web.session_token` no longer redeclares or directly calls
`rt_random_hex`. Token IDs and development-secret entropy use the canonical
checked CSPRNG facade, which preserves the existing fail-closed unwrap while
also rejecting missing, wrong-length, non-lowercase-hex, or all-zero output.
Issuance still performs exactly one provider call. The additional validation
is one bounded linear scan (64 characters for a token ID, 16 for the current
development-secret request) with no copy, lookup, retry, or allocation.

The focused static ratchet passed. Production execution remains blocked by the
policy-rejected bootstrap runtime, and exact-artifact admission remains zero.
One duplicate declaration row is removed: 11,983 rows / 3,156 symbols, 1,189
tagged, 637 `unsafe_contract_declared`, 10,528 untouched, and zero signed.

## Credential-store entropy-owner checkpoint

Credential key-salt and AES-CBC IV generation now use the canonical checked
CSPRNG owner instead of a local `rt_random_hex` declaration. Both paths retain
their existing nullable fail-closed behavior and exactly one provider call per
fresh salt or IV. Canonical validation adds only bounded scans of the returned
32-character strings and no copy, lookup, retry, or allocation. The existing
JIT re-materialization workaround remains untouched after validation.

The focused static ratchet passed; executable and signed-artifact admission
remain unavailable. One declaration row is removed: 11,982 rows / 3,156
symbols, 1,189 tagged, 637 `unsafe_contract_declared`, 10,527 untouched, and
zero exact-artifact verified-and-signed.

## WebSocket entropy-result checkpoint

Browser WebSocket handshake keys and client-frame masks now use canonical
checked entropy. The local non-null `rt_random_hex` declaration is removed;
both generators return browser `Result`, and the connect/send/receive-control/
close/ping callers propagate failure before emitting an unmasked or predictable
frame. Success performs exactly one CSPRNG call and the existing counter mix.
Validation scans only 32 handshake-key hex characters or 8 mask characters;
there is no retry, lookup, generic dispatch, or additional entropy buffer.

The focused static ratchet passed. Production execution and signed admission
remain blocked as recorded above. One declaration row is removed: 11,981 rows
/ 3,156 symbols, 1,189 tagged, 637 `unsafe_contract_declared`, 10,526
untouched, and zero exact-artifact verified-and-signed.

## OAuth entropy-result checkpoint

The no-GC sync, no-GC async, and GC async OAuth variants no longer redeclare
or call `rt_random_hex`, and they no longer substitute `"0"` when entropy is
unavailable. `random_int`, random-string generation, CSRF state, timestamped
state, PKCE verifier, and mock-token creation now return and propagate typed
`Result` failures. The OAuth entropy spec uses the canonical checked facade
rather than bypassing it with another raw declaration.

Success retains the previous one CSPRNG draw per generated character and stops
immediately on failure. Each draw now includes the canonical bounded
16-character validation scan; there is no retry, payload copy, lookup, generic
dispatch, or added random draw. The focused static ratchet passed. Production
execution and exact-artifact admission remain unavailable.

Three declaration rows are removed: 11,978 rows / 3,156 symbols, 1,189 tagged,
637 `unsafe_contract_declared`, 10,523 untouched, and zero exact-artifact
verified-and-signed.

## Security correlation-ID entropy checkpoint

`security.types` no longer redeclares `rt_random_hex` or converts missing
entropy to an empty suffix. Correlation IDs use the canonical checked owner and
fail closed on nil/malformed/all-zero entropy, preserving the existing `text`
constructor API without fabricating a timestamp-only identifier. Across the
repository, `rt_random_hex` now has exactly one declaration and one lexical
call, both in the canonical crypto facade.

The success path remains one provider call plus a bounded 16-character scan,
with no copy, retry, lookup, generic dispatch, or allocation added. The static
ratchet passed. Production execution and signed admission remain unavailable.
One declaration row is removed: 11,977 rows / 3,156 symbols, 1,189 tagged, 637
`unsafe_contract_declared`, 10,522 untouched, and zero exact-artifact
verified-and-signed.

## Application TLS facade consolidation checkpoint

`app.io.tls_sffi` was a second copy of the canonical TLS module: the same 35
raw declarations and wrappers, differing only because the application copy did
not export its surface directly. It is now a compatibility re-export of
`std.nogc_sync_mut.io.tls_sffi`, and `app.io.tls_ffi` continues to select its
named safe facade from that path.

This is a zero-runtime-cost consolidation: no TLS provider call, branch,
allocation, copy, lookup, or handshake behavior changes. The focused TLS
fail-closed/static-owner ratchet passed. Production execution and signed
admission remain unavailable. Thirty-five duplicate declaration rows are
removed: 11,942 rows / 3,156 symbols, 1,189 tagged, 637
`unsafe_contract_declared`, 10,487 untouched, and zero exact-artifact
verified-and-signed.

## TLS-disabled native provider removal checkpoint

The Rust runtime previously included `net_tls_stub.rs` whenever `runtime-tls`
was disabled. That file exported the full TLS symbol family while returning
`-1`, empty text, or `false`; in particular, a missing provider read was
indistinguishable from clean EOF. The stub module is deleted, its include is
removed, and TLS re-exports from both runtime layers are gated by the real
`runtime-tls` feature. A TLS-disabled runtime can still build, but an artifact
requiring TLS now fails linkage/admission instead of receiving fabricated
values.

The TLS-enabled implementation is unchanged, so there is no added branch,
lookup, allocation, copy, or call overhead. `cargo check` passed once for both
`--no-default-features` and `--no-default-features --features runtime-tls`.
The TLS static fail-closed ratchet also passed. This changes provider behavior,
not Simple declaration inventory, so the ledger remains 11,942 rows / 3,156
symbols, 1,189 tagged, 637 `unsafe_contract_declared`, 10,487 untouched, and
zero exact-artifact verified-and-signed.

## TLS client checked-read checkpoint

The rustls client provider previously returned empty text for invalid input,
unknown handles, socket-timeout setup failure, read failure, and clean EOF.
`rt_tls_client_read_checked` now returns `nil` for the failure cases while
retaining empty text for clean EOF. The web TLS client consumes that nullable
contract and maps only `nil` to `Result.Err`; legitimate empty reads remain
`Result.Ok("")`. The legacy symbol remains available for unmigrated callers.

Both entry points share one implementation. The checked success path keeps one
handle lookup, one bounded buffer allocation, one socket read, and one text
lift; it adds no descriptor, copy, retry, generic dispatch, or symbol lookup.
The legacy path adds only a failure-path conversion to its historical empty
sentinel. The TLS static ratchet, both runtime feature compile checks, and the
focused runtime and interpreter bridge tests passed. The compiler now selects
the real `runtime-tls` provider explicitly, and its compile check passed; this
prevents fake-stub removal from leaving registered interpreter handlers without
implementations. Rust formatting remains WARN
because unrelated `wsffi_native.rs` and surrounding export lists were already
not rustfmt-clean; they were not absorbed into this lane.

One tagged declaration/symbol is added for the checked ABI: 11,943 rows / 3,157
symbols, 1,190 tagged, 638 `unsafe_contract_declared`, 10,487 untouched, and
zero exact-artifact verified-and-signed. The broader TLS/SFFI surface remains
unsafe and unadmitted.

## TLS server checked-read checkpoint

The rustls server read now has the same explicit three-state contract as the
client: checked failure is `nil`, clean EOF is empty text, and data is nonempty
text. Hosted legacy and checked symbols share one inlineable implementation;
the compile-time checked flag is consulted only on failure paths. Successful
reads retain one handle lookup, one bounded buffer allocation, one socket read,
and one text lift with no added copy, descriptor, retry, lookup, or dispatch.

The web serve loop now imports the checked canonical declaration, reports I/O
failure separately from EOF, and no longer redeclares the byte-write provider.
The canonical friendly server-read wrapper is `Result<text,text>` and cannot
manufacture empty text for an invalid handle. SimpleOS exports the same checked
symbol and returns `nil` because its live netstack provider is unavailable.

The focused static audit and hosted client/server failure-identity test passed.
Production Simple checking remains unavailable under the repository runtime
policy and was not replaced with a seed run. Adding one canonical tagged
declaration while deleting one application duplicate keeps 11,943 declaration
rows; there are now 3,158 symbols, 1,191 tagged declarations, 639
`unsafe_contract_declared`, 10,486 untouched, and zero exact-artifact
verified-and-signed.

## TLS accept/write/close typed-wrapper checkpoint

The hosted provider already reports accept/write failure with a negative i64
and close outcome with a semantic boolean. No replacement numeric convention
or second provider ABI was needed. The canonical client write/read/close and
server accept/write/read/close wrappers now return typed `Result` values rather
than manufacturing zero, false, empty text, or an invalid resource object.
The mail and web-server callers propagate or explicitly handle those results.

Web accept/write/close helpers retain one provider call and move their existing
status branch into the helper. `Result.Ok` carries the existing scalar/resource
directly; no payload copy, retry, lookup, descriptor, generic dispatch, or heap
buffer was introduced. The Rust provider is unchanged. The canonical raw
accept/write/read/close declarations now carry minimal `unsafe(ffi)` contract
tags, and the previously missing canonical byte-write declaration replaces the
application-local duplicate removed in the preceding slice.

The focused static gate passed. Production Simple checking and optimizer
evidence remain unavailable under the repository runtime policy. The estimate
is now 11,944 declaration rows / 3,158 symbols, 1,199 tagged declarations, 647
`unsafe_contract_declared`, 10,479 untouched, and zero exact-artifact
verified-and-signed.

## TLS constructor and shutdown typed-wrapper checkpoint

Canonical client connect/SNI connect and server create no longer return invalid
resource objects on provider failure; they return typed `Result` values.
Server shutdown similarly maps the provider's semantic boolean to `Result<()>`
instead of exposing false as an ambiguous safe outcome. Mail and web startup
callers now pattern-match those results. Raw provider semantics remain negative
handle sentinels and boolean shutdown status; no boolean was converted to an
integer and no new ABI was introduced.

Each success path still performs one provider call and its existing handle or
boolean branch. Result construction adds no payload copy, retry, lookup,
descriptor, generic dispatch, or foreign allocation. The four raw constructor/
shutdown declarations now carry minimal `unsafe(ffi)` contract tags. The
focused static ratchet passed; production Simple/optimizer evidence remains
unavailable under policy.

The estimate remains 11,944 declaration rows / 3,158 symbols, with 1,203 tagged
declarations, 651 `unsafe_contract_declared`, 10,475 untouched, and zero
exact-artifact verified-and-signed.

## Fabricated TLS configuration provider removal checkpoint

The six client-configuration and four server-configuration symbols had no
callers and no provider state. Hosted implementations returned synthetic
handles or unconditional `true`; SimpleOS exported corresponding unavailable
stubs. All ten symbols are now removed from the canonical facade, hosted
provider exports, compiler runtime-symbol registry, and SimpleOS.

Removal is preferable to an unused compatibility subsystem: it eliminates
advertised false capability and adds no handle table, allocation, lock, lookup,
branch, or release path. The static absence ratchet passed, and both TLS-disabled
and TLS-enabled runtime compile checks passed once.

The estimate falls to 11,934 declaration rows / 3,148 symbols, with 1,203
tagged declarations, 651 `unsafe_contract_declared`, 10,465 untouched, and
zero exact-artifact verified-and-signed.

## Fabricated TLS certificate provider removal checkpoint

Ten unused certificate/peer/self-sign/hash symbols were advertised without an
implementation: hosted code returned synthetic handles, empty metadata,
unconditional release success, or guaranteed failure, while SimpleOS exported
equivalent unavailable stubs. They are removed from the canonical facade,
hosted exports, compiler runtime registry, and SimpleOS. The now-unused atomic
fake-handle generator is also removed. Application, async, and library-root
compatibility facades no longer re-export the removed types or functions.

Connection info no longer calls a fabricated peer-certificate handle path;
`peer_cert_subject` is explicitly optional and currently `nil`. Removing these
paths reduces code and static state and introduces no provider call, allocation,
lock, lookup, branch, or dispatch. The static absence ratchet and both runtime
feature compile configurations passed once.

The estimate falls to 11,924 declaration rows / 3,138 symbols, with 1,203
tagged declarations, 651 `unsafe_contract_declared`, 10,455 untouched, and
zero exact-artifact verified-and-signed.

## Truthful TLS connection metadata checkpoint

Protocol, cipher, ALPN, and handshake providers no longer fabricate `"tcp"`,
empty cipher metadata, or unconditional `true`. Invalid/stale/incomplete
connections return `nil`; ALPN uses empty text only for the valid ordinary
"not negotiated" outcome. Handshake presence is optional while its contained
value remains a semantic boolean. Canonical safe wrappers lift metadata and
handshake state into typed `Result` values, and browser/interpreter callers
handle absence explicitly.

Cipher names are selected from static literals for the rustls ring-supported
suites. The provider performs no `format!`, temporary `String`, or second text
copy. Existing table lookup/lock count and provider-call count are unchanged;
each returned text uses the existing single runtime text lift. The static
ratchet, compiler check, and focused invalid-handle metadata test passed.

Declaration and symbol totals remain 11,924 / 3,138. Five formerly untagged
raw declarations are now minimally `unsafe(ffi)`: 1,208 tagged declarations,
656 `unsafe_contract_declared`, 10,450 untouched, and zero exact-artifact
verified-and-signed.

## Browser TLS canonical checked-owner checkpoint

`browser_net_runtime` no longer redeclares TLS providers. It imports the
canonical owner and uses checked nullable reads plus the real address-connect,
write, and checked-read timeout ABIs. The previous branches ignored every
timeout and called the non-timeout provider in both arms; they are removed.
Browser transport helpers and `TlsConnection` now return typed `Result` values
for connect/read/write/close, preserving empty text as clean EOF.

Each operation performs exactly one provider call. There is no retry, timer
task, generic lookup, second buffer, or payload copy. Checked timeout read uses
the same internal single-read implementation as the other client reads. The
static owner/timeout ratchet, compiler integration check, and focused checked
read test passed.

Adding three canonical timeout declarations, removing five browser-local TLS
declarations, and adding two non-TLS raw authority tags yields an estimated
11,922 declaration rows / 3,139 symbols, 1,212 tagged declarations, 660
`unsafe_contract_declared`, 10,446 untouched, and zero exact-artifact
verified-and-signed.

## Ambiguous TLS read provider removal checkpoint

After browser migration, no Simple caller remained for legacy client read,
client timeout-read, or server read. Those three providers are removed from
hosted exports, interpreter registration, native symbol tables, canonical
declarations, and SimpleOS. Only nullable checked reads remain. SimpleOS now
also exports fail-closed checked client read/timeout and the real timeout symbol
family required by sealed consumers.

This deletion reduces code and dispatch surface. It adds no compatibility
branch, lookup, allocation, copy, or provider call. The static checked-only
ratchet, compiler integration check, and focused invalid-handle read test
passed; only pre-existing compiler warnings remain.

Removing two canonical declarations and three unique symbols yields an
estimated 11,920 declaration rows / 3,136 symbols, 1,210 tagged declarations,
658 `unsafe_contract_declared`, 10,446 untouched, and zero exact-artifact
verified-and-signed.

## Graphics2D canonical-owner consolidation checkpoint

`app.io.graphics2d_sffi` duplicated the full 510-line canonical module and its
49 `rt_lyon_*` declarations. Its only semantic difference was weaker handle
validation: it accepted every negative handle as valid via `handle != 0`, while
the canonical owner requires `handle > 0`. The application module is now a
two-line compatibility re-export of `std.nogc_sync_mut.io.graphics2d_sffi`.

This removes duplicate declarations and the negative-handle divergence with no
runtime call, branch, allocation, copy, lookup, or layout change. A dedicated
owner ratchet requires exactly 49 declarations in the canonical file and
forbids providers, wrappers, or `handle != 0` semantics in the application
facade; it passed.

Based on the authoritative inventory immediately before this consolidation,
the estimate is 11,870 `rt_*` declaration rows / 3,135 symbols, 1,210 tagged,
10,402 untouched, and zero exact-artifact verified-and-signed.

## Graphics2D raw-contract ownership checkpoint

All 49 declarations in the canonical Lyon owner now carry an adjacent,
operation-specific `@unsafe(... capabilities: [ffi])` contract. The annotations
identify handle, tuple, array, text, count, and failure-sentinel ABI families;
they do not claim semantic verification or signed-artifact admission. The owner
ratchet now requires all 49 declarations to remain explicitly tagged.

This is compile-time metadata only. It changes no foreign signature, wrapper,
branch, lookup, allocation, copy, data layout, or provider call. The owner
ratchet and diff whitespace check passed. The unavailable production
self-hosted runtime means no new Simple compiler or optimizer claim is made.

Relative to the preceding authoritative inventory, totals remain 11,870
`rt_*` declaration rows / 3,135 symbols. Unsafe-tagged rows increase from 1,210
to 1,259, untouched rows decrease from 10,402 to 10,353, and exact-artifact
verified-and-signed admission remains zero. The existing wrappers still encode
some invalid-handle failures as dummy resources, zeros, empty arrays, or
booleans; those APIs require typed failure migration before they can be called
safe.

## SIMD raw-contract ownership checkpoint

The canonical SIMD module's 49 raw declarations now carry adjacent
`@unsafe(... capabilities: [ffi])` contracts. The contracts distinguish target
feature queries, profile discriminants and text, mutable bulk array copying,
fixed-width vector operations, shifts, fused operations, and reductions. A new
static ratchet fixes the reviewed inventory at 49 and requires every declaration
to retain its FFI capability tag.

This pass deliberately does not wrap or redirect an intrinsic: no signature,
dispatch tier, call count, branch, allocation, copy, vector layout, or fallback
behavior changed. That preserves the SIMD hot path and avoids laundering an ABI
boundary into a slower generic adapter. The static ratchet and whitespace check
passed; no production-runtime or optimizer claim is made while the self-hosted
runtime remains unavailable.

Totals remain 11,870 `rt_*` declaration rows / 3,135 symbols. Unsafe-tagged
rows increase from 1,259 to 1,308, untouched rows decrease from 10,353 to
10,304, and exact-artifact verified-and-signed admission remains zero. These
annotations identify unsafe ownership only; exact target ABI fingerprints and
signed provider admission are still required before SIMD can be called fully
verified.

## Rapier2D canonical-owner consolidation checkpoint

`app.io.rapier2d_sffi` duplicated the canonical 472-line Rapier2D wrapper and
all 48 `rt_rapier2d_*` declarations. The app copy's only semantic divergence
was weaker validation at nine resource-construction sites: `handle != 0`
accepted negative provider error sentinels, while the canonical library owner
requires `handle > 0`. The app module is now a two-line compatibility re-export
of `std.nogc_sync_mut.io.rapier2d_sffi`.

This removes a duplicate foreign boundary and selects the stricter existing
semantics. It adds no runtime call, branch, lookup, allocation, copy, or layout
change. A static owner ratchet requires exactly 48 declarations in the
canonical owner and forbids declarations, wrappers, or negative-handle
acceptance in the app facade; it passed with the whitespace check.

Totals decrease from 11,870 to 11,822 `rt_*` declaration rows while unique
symbols remain 3,135. Unsafe-tagged rows remain 1,308, untouched rows decrease
from 10,304 to 10,256, and exact-artifact verified-and-signed admission remains
zero. The canonical Rapier2D declarations and fallible wrapper returns still
need contract tagging and typed-error review.

## Rapier2D raw-contract ownership checkpoint

All 48 declarations in the canonical Rapier2D owner now carry adjacent,
operation-specific `@unsafe(... capabilities: [ffi])` contracts. The metadata
identifies world, body, collider, contact-list, and joint handle families;
tuple, tagged-tuple, array, scalar/count, boolean-status, and error-text return
families; and the nonpositive or negative failure sentinels where applicable.
The owner ratchet now requires all 48 declarations to remain explicitly tagged.

This changes no foreign signature, wrapper, call count, dispatch, branch,
allocation, copy, or resource layout. The physics simulation and query hot
paths remain direct. The static owner ratchet and whitespace check passed; no
production-runtime or optimizer claim is made while the self-hosted runtime is
unavailable.

Totals remain 11,822 `rt_*` declaration rows / 3,135 symbols. Unsafe-tagged
rows increase from 1,308 to 1,356, untouched rows decrease from 10,256 to
10,208, and exact-artifact verified-and-signed admission remains zero. The raw
tags identify the unsafe boundary but do not make dummy-resource, zero-tuple,
or boolean failure wrappers typed or verified.

## Metal symbol-identity collision checkpoint

Metal review found that `rt_metal_create_device` and `rt_metal_present` did not
have one repository-wide ABI. The canonical owner declares indexed device
creation and boolean presentation, while the GPU-session facade redeclared
zero-argument creation and text presentation under the same symbol names. The
Engine2D session also redeclared device creation and compute-pipeline creation
with incompatible signatures. A linker could therefore resolve a valid symbol
whose calling contract belonged to a different consumer.

The two unadmitted pseudo-provider families now use scoped
`rt_gpu_session_metal_*` and `rt_engine2d_metal_session_*` identities. All 14
declarations are explicitly `unsafe(ffi)` and state that their providers are
not admitted. Missing providers now fail symbol resolution rather than
accidentally binding to an incompatible canonical Metal implementation. A
static audit rejects restoration of the colliding declarations and fixes both
pseudo-provider inventories.

The rename changes no successful provider call, branch, allocation, copy, or
GPU data path because no matching provider implementations were found for the
pseudo-provider contracts. It removes an ABI-confusion path rather than adding
a compatibility adapter. Declaration totals remain unchanged; 14 previously
untagged rows are now unsafe-tagged. An authoritative unique-symbol recount is
required after the complete Metal pass because separating formerly colliding
identities intentionally changes symbol cardinality. Exact-artifact signed
admission remains zero.

## Canonical Metal contract and fabricated-stub checkpoint

The canonical Metal owner now has 40 raw declarations, all with adjacent,
operation-specific `@unsafe(... capabilities: [ffi])` contracts. They cover
runtime/device queries, resource handles, borrowed and mutable byte arrays,
shader text, command submission, blocking completion, raw parameter pointers,
batched compute status, and nullable error C strings. The static audit requires
all 40 declarations to retain their tags.

Three additional declarations lived under an explicit `Graphics — Missing
Stubs` heading. Their Rust providers always returned integer zero for sampler
creation, swapchain creation, and presentation, while the Simple facade exposed
dummy resource objects and a boolean presentation result. No consumer existed
outside an async compatibility re-export. The declarations, dummy wrappers,
types, and re-exports are removed rather than converting zero to `false` or
claiming an unsafe stub is a functional API.

The change adds no provider call, dispatch, branch, allocation, copy, or GPU
data movement. It deletes fabricated surface and adds compile-time metadata to
the remaining direct calls. The Metal identity/contract audit and whitespace
check passed; production Simple and optimizer verification remain unavailable.
The refreshed source-only authoritative inventory reports 11,819 `rt_*`
declaration rows / 3,138 `rt_*` symbols, 1,410 unsafe-tagged rows, 10,151
untouched rows, and zero exact-artifact verified-and-signed admissions. The
inventory artifacts are retained at
`/mnt/data/tmp/sffi-inventory.pNuueT/{contracts,symbols}.tsv`.

## Debug canonical-owner consolidation checkpoint

`std.nogc_sync_mut.ffi.debug` duplicated all 43 raw declarations and nearly all
wrapper code from `std.nogc_sync_mut.sffi.debug`. Its differences were naming
comments, one annotation's wording, and the absence of the canonical explicit
export list; no direct consumer of the duplicate namespace was found. The FFI
module is now a two-line compatibility re-export of the canonical SFFI owner.

This removes duplicate declarations and wrapper maintenance without adding a
runtime call, branch, lookup, allocation, copy, or layout change. A static
owner ratchet fixes the canonical inventory at 43 and forbids providers or
wrappers in the compatibility facade; it passed with the whitespace check.

Relative to the refreshed authoritative baseline, estimated `rt_*` declaration
rows decrease from 11,819 to 11,776 while unique symbols remain 3,138.
Unsafe-tagged rows remain 1,410, untouched rows decrease from 10,151 to 10,108,
and exact-artifact verified-and-signed admission remains zero. The 43 canonical
debug declarations remain the next contract-tagging target.

## Debug raw-contract ownership checkpoint

All 43 canonical debug declarations now carry adjacent, operation-specific
`@unsafe(... capabilities: [ffi])` contracts. The metadata distinguishes
debugger global and stack mutation, blocking synchronization, borrowed
pointer/length text inputs, runtime-owned text, OS ptrace process control,
register-map and process-memory ownership, blocking wait status, and owned
DWARF handle/string-array lifetimes. The owner ratchet now requires all 43 raw
declarations to remain explicitly tagged.

This is compile-time ownership metadata only. It changes no syscall, debugger
wait, provider call, allocation, process-memory copy, dictionary/array layout,
or wrapper result. The owner ratchet and whitespace check passed; production
Simple and optimizer verification remain unavailable.

Totals remain an estimated 11,776 `rt_*` declaration rows / 3,138 symbols.
Unsafe-tagged rows increase from 1,410 to 1,453, untouched rows decrease from
10,108 to 10,065, and exact-artifact verified-and-signed admission remains
zero. Raw ptrace and DWARF APIs remain unsafe until their status, absence,
ownership, platform policy, and exact provider evidence are fully admitted.

## CLI canonical-owner and raw-contract checkpoint

`std.nogc_sync_mut.ffi.cli` duplicated all 40 declarations and wrappers from
canonical `std.nogc_sync_mut.sffi.cli`, except that it renamed the generator
surface to `rt_cli_run_ffi_gen`. Repository-wide provider inspection found no
runtime, interpreter, or codegen implementation for that symbol; only
`rt_cli_run_sffi_gen` is implemented and registered. The FFI namespace is now a
canonical re-export with two legacy source-level aliases that call the real
SFFI generator. This eliminates unresolved foreign dispatch while retaining
the legacy function names.

All 40 canonical declarations now carry adjacent, operation-specific
`@unsafe(... capabilities: [ffi])` contracts covering process arguments and
termination, filesystem reads/watches, compiler tagged tuples, command text
and argument arrays, and command exit-status families. The static ratchet
requires all 40 tags, forbids provider declarations in the compatibility
facade, and rejects reintroduction of `rt_cli_run_ffi_gen`; it passed with the
whitespace check.

This removes 40 duplicate foreign declarations. It adds no foreign call,
allocation, array copy, lookup, or command dispatch; only the two cold legacy
generator aliases have one ordinary Simple forwarding call. Estimated totals
are 11,736 `rt_*` declaration rows / 3,137 symbols, 1,493 unsafe-tagged rows,
9,985 untouched rows, and zero exact-artifact verified-and-signed admissions.

## GLFW raw-contract ownership checkpoint

All 40 declarations in the canonical GLFW-shaped hosted adapter now carry
adjacent, operation-specific `@unsafe(... capabilities: [ffi])` contracts. The
metadata identifies borrowed title and clipboard text, window handles and
status returns, runtime-owned event/clipboard text, stateful current-event
snapshots, event/window counts, blocking/global operations, and both ARGB
presentation families. The array form requires dimensions to fit its pixels;
the raw pointer form requires the supplied count to cover the dimensions.

A static ratchet fixes the reviewed inventory at 40 and requires one adjacent
FFI tag per declaration. It passed with the whitespace check. This pass changes
no signature, presentation/event call count, branch, allocation, copy, buffer
layout, event storage, or lookup, so frame and input hot paths are unchanged.
Production Simple and optimizer verification remain unavailable.

Estimated totals remain 11,736 `rt_*` declaration rows / 3,137 symbols.
Unsafe-tagged rows increase from 1,493 to 1,533, untouched rows decrease from
9,985 to 9,945, and exact-artifact verified-and-signed admission remains zero.
The tags do not prove GLFW pointer lifetimes, extent checks, or provider
identity; those require executable contracts and exact signed admission.

## Compiler minimal-runtime raw-contract checkpoint

The compiler's minimal runtime ABI contains 41 declarations, not 40: the
source-only untouched ranking showed 40 because one declaration already had
recognized contract state. All 41 now carry adjacent, operation-specific
`@unsafe(... capabilities: [ffi])` contracts. The metadata distinguishes GC
mutation and allocation, owned runtime-value construction/cloning/release,
borrowed pointer/length strings, discriminants and projections, arithmetic
owned results, tagged-string and exclusive deep-array release, filesystem
pointer/length operations, and environment pointer/length operations.

A static ratchet fixes the inventory at 41 and requires every declaration to
retain its tag. It passed with the whitespace check. This pass changes no ABI
signature, allocation, clone, free, collection traversal, filesystem or
environment call, branch, copy, or runtime-value layout; core hot paths remain
unchanged. Production Simple and optimizer verification remain unavailable.

Estimated totals remain 11,736 `rt_*` declaration rows / 3,137 symbols.
Unsafe-tagged rows increase from 1,533 to 1,573, untouched rows decrease from
9,945 to 9,905, and exact-artifact verified-and-signed admission remains zero.
The raw string out-length and pointer ownership contracts still require typed
ABI validation before this module can be called safe.

## Audio raw-contract ownership checkpoint

The canonical audio owner contains 39 declarations; one pitch contract was
already tagged, and the remaining 38 now carry adjacent, operation-specific
`@unsafe(... capabilities: [ffi])` metadata. The contracts cover engine,
source, playback, SDL2-device, and capture-session handles; path and backend
text; live/queued/frame/underrun counts; spatial listener/source state; and PCM
array or raw pointer/count inputs. The PCM contracts explicitly require the
array or pointed storage to cover the declared sample/channel/frame extent.

A static ratchet fixes the inventory at 39 and requires every declaration to
remain tagged. It passed with the whitespace check. This pass changes no ABI
signature, playback/queue call count, callback, sample conversion, allocation,
buffer copy, queue query, or audio data layout; latency-sensitive paths remain
unchanged. Production Simple and optimizer verification remain unavailable.

Estimated totals remain 11,736 `rt_*` declaration rows / 3,137 symbols.
Unsafe-tagged rows increase from 1,573 to 1,611, untouched rows decrease from
9,905 to 9,867, and exact-artifact verified-and-signed admission remains zero.
Executable extent validation and exact provider evidence remain required before
raw PCM or generation-handle operations can be treated as verified-safe.

## Bootstrap allocation raw-contract checkpoint

All 37 declarations in the bootstrap standard library allocation module now
carry adjacent, operation-specific `@unsafe(... capabilities: [ffi])` metadata.
The contracts distinguish owned heap pointers and reallocation failure,
runtime array/dictionary handles and mutation, owned result handles, untyped
pop/get/lookup absence sentinels, dynamic `Any` dictionary keys, runtime text
ownership, string-derived array handles, and in-place collection operations.

A static ratchet fixes the inventory at 37 and requires every declaration to
retain its tag. It passed with the whitespace check. This pass changes no ABI
signature, allocation/reallocation/free call, collection traversal, clone,
string transformation, branch, copy, handle layout, or dispatch. Core memory
and collection hot paths remain unchanged; production Simple and optimizer
verification remain unavailable.

Estimated totals remain 11,736 `rt_*` declaration rows / 3,137 symbols.
Unsafe-tagged rows increase from 1,611 to 1,648, untouched rows decrease from
9,867 to 9,830, and exact-artifact verified-and-signed admission remains zero.
The dynamic-key ABI and untyped collection absence/error returns must be
replaced by canonical typed contracts before safe publication.

## Simple-core process/time/panic raw-contract checkpoint

All 36 raw libc/runtime declarations in `simple-core` process support now carry
adjacent, operation-specific `@unsafe(... capabilities: [ffi])` metadata. The
contracts cover process termination, fork/exec/wait and process groups, signal
handlers and signal-set pointers, time output structures, heap allocation,
unchecked pointer/offset loads and stores, NUL-terminated string pointers,
tagged string/array/tuple values, and owned argument-array value transfer.

A static ratchet fixes the inventory at 36 and requires every declaration to
retain its tag. It passed with the whitespace check. This pass changes no ABI
signature, fork/exec/signal/time call, allocation/free, pointer access,
argument construction, collection operation, branch, copy, or layout.
Production Simple and optimizer verification remain unavailable.

Estimated totals remain 11,736 `rt_*` declaration rows / 3,137 symbols.
Unsafe-tagged rows increase from 1,648 to 1,684, untouched rows decrease from
9,830 to 9,794, and exact-artifact verified-and-signed admission remains zero.
Signal-handler validity, pointer extents, post-fork restrictions, and exact
libc/runtime identity still require executable policy and admission evidence.

## Simple-core string/stdio raw-contract checkpoint

All 35 raw declarations in `simple-core` string and string-backed stdio now
carry adjacent, operation-specific `@unsafe(... capabilities: [ffi])` metadata.
The contracts cover heap ownership, memory copy/compare extents, integer/float
parsing with end-pointer outputs, NUL-terminated strings, file-descriptor
pointer/count I/O, unchecked pointer/offset access, tagged array/dictionary
handles, borrowed array item pointers, owned value construction, and enum
identity/discriminant/borrowed-payload projections.

A static ratchet fixes the inventory at 35 and requires every declaration to
retain its tag. It passed with the whitespace check. This pass changes no ABI
signature, registry scan, allocation/reallocation/free, parsing operation,
syscall, memory copy, collection traversal, branch, value layout, or dispatch.
The compact string registry and all string hot paths remain unchanged;
production Simple and optimizer verification remain unavailable.

Estimated totals remain 11,736 `rt_*` declaration rows / 3,137 symbols.
Unsafe-tagged rows increase from 1,684 to 1,719, untouched rows decrease from
9,794 to 9,759, and exact-artifact verified-and-signed admission remains zero.
Pointer extents, parsing end-pointer validity, and borrowed payload lifetimes
still require executable validation and exact provider admission.

## Simple-core filesystem raw-contract checkpoint

All 34 raw declarations in `simple-core` filesystem support now carry adjacent,
operation-specific `@unsafe(... capabilities: [ffi])` metadata. The contracts
cover heap ownership, NUL-terminated paths and modes, FILE/DIR/descriptor
handles, stdio element extents, descriptor buffer extents, mmap address/length
lifetime, borrowed `dirent` pointers, rename/remove paths, tagged string/array
results, value transfer, and unchecked pointer/offset access.

A static ratchet fixes the inventory at 34 and requires every declaration to
retain its tag. It passed with the whitespace check. This pass changes no ABI
signature, path copy/normalization, allocation/free, file or directory syscall,
read/write count, mmap operation, directory scan, buffer copy, branch, or
layout. Production Simple and optimizer verification remain unavailable.

Estimated totals remain 11,736 `rt_*` declaration rows / 3,137 symbols.
Unsafe-tagged rows increase from 1,719 to 1,753, untouched rows decrease from
9,759 to 9,725, and exact-artifact verified-and-signed admission remains zero.
Partial-I/O, mmap failure sentinels, directory-entry lifetime, and exact libc
identity still require executable validation and signed admission.

## Hosted Winit canonical-owner checkpoint

`os.hosted.hosted_entry` locally redeclared 30 Winit functions. Six were absent
from the canonical owner, while overlapping declarations disagreed on ABI:
event/window/loop release returned `bool` canonically but was declared void in
hosted entry, and fullscreen read/write returned `bool` canonically but was
declared `i64` locally. The six missing scancode, shifted-key, wheel-x, native
surface-kind, native-display, and native-window contracts are now canonical,
and hosted entry imports all 30 symbols directly from that owner.

Hosted fullscreen logic now uses the canonical boolean values rather than
numeric comparisons/conversions. This fixes the declared ABI instead of
representing booleans as numbers. The four irreducible wall-clock, monotonic
clock, nullable environment, and argument-array declarations remain local and
are explicitly `unsafe(ffi)`.

The owner audit requires 35 tagged canonical Winit declarations, forbids local
Winit externs, fixes the four local declarations, and rejects numeric boolean
adaptation. It passed with the whitespace check. No wrapper, event poll,
provider call, branch, allocation, buffer copy, or render/event data-layout
change was added. Estimated totals decrease from 11,736 to 11,712 declaration
rows while symbols remain 3,137; unsafe-tagged rows become 1,762, untouched
rows become 9,692, and exact signed admission remains zero.

## TLS 1.3 context raw-contract checkpoint

All 48 declarations in the TLS 1.3 context I/O module now carry adjacent,
operation-specific `@unsafe(... capabilities: [ffi])` metadata. The contracts
cover network and IPC transport, blocking sleep, record receive/parsing,
byte-array indexing/allocation, ClientHello and X25519, HKDF and secret caches,
SHA-256/transcript/HMAC derivation, encrypted handshake extraction, record
metadata, certificate/key/signature parsing, and inner-plaintext decoding.

The metadata explicitly identifies ambiguous empty-array failures, untyped
parser/status/discriminant sentinels, cache-take ownership, and the numeric
byte-equality result. It does not treat empty bytes or zero as verified success.
A static ratchet fixes the inventory at 48 and requires every declaration to
retain its tag; it passed with the whitespace check.

This pass changes no ABI signature, network/IPC call, hash, HMAC, HKDF, key
agreement, record parse, allocation, byte-array copy, cache lookup, branch, or
cryptographic data layout. Production Simple and optimizer verification remain
unavailable. Estimated totals remain 11,712 declaration rows / 3,137 symbols;
unsafe-tagged rows increase from 1,762 to 1,810, untouched rows decrease from
9,692 to 9,644, and exact signed admission remains zero.

## Authoritative inventory refresh after TLS context

The refreshed source-only inventory reports 11,713 `rt_*` declaration rows and
3,137 `rt_*` symbols. Of those rows, 1,737 are unsafe-tagged, 9,720 remain
untouched, and zero are exact-artifact verified-and-signed admissions. The
broader all-extern ledger contains 13,475 rows / 3,936 symbols, with 1,922
unsafe-tagged and 11,060 untouched. These authoritative classifications replace
the intervening arithmetic estimates, which cannot account for every
non-`rt_*`, predeclared-contract, or shared-symbol classification.

The inventory artifacts are retained at
`/mnt/data/tmp/sffi-inventory.F4tIYb/{contracts,symbols}.tsv`. The largest owned
production untouched file is now bootstrap `infra/file_io.spl` with 33 rows;
tests and duplicated test layouts remain separately visible but do not outrank
production boundary ownership work.

## Bootstrap file-I/O raw-contract checkpoint

The bootstrap `infra/file_io.spl` owner contains 35 declarations; two optional
read returns already had recognized contract state, and all declarations now
carry adjacent, operation-specific `@unsafe(... capabilities: [ffi])` metadata.
The contracts cover path metadata, optional text-line/byte reads, text and byte
writes, atomic/append operations, copy/move/rename/remove, canonical paths,
directory list/glob/walk and recursive mutation, path decomposition/joining,
current-directory state, and file-descriptor open/size/close.

The metadata identifies ambiguous non-optional empty text/list results rather
than treating them as proven success. A static ratchet fixes the inventory at
35 and requires every declaration to retain its tag; it passed with the
whitespace check. No preflight call, filesystem operation, recursive scan,
allocation, buffer copy, path normalization, branch, or descriptor operation
was added. Production Simple and optimizer verification remain unavailable.

Relative to the refreshed authoritative baseline, declaration rows and symbols
remain 11,713 / 3,137. Unsafe-tagged rows increase from 1,737 to 1,770,
untouched rows decrease from 9,720 to 9,687, and exact signed admission remains
zero. Non-optional empty results still require typed `Result` migration.

## Runtime canonical-owner consolidation checkpoint

`std.nogc_sync_mut.ffi.runtime` duplicated the canonical
`std.nogc_sync_mut.sffi.runtime` module's 32 raw declarations and wrappers; the
only differences were the heading comments. No direct consumer of the duplicate
namespace was found. The FFI module is now a two-line compatibility re-export
of the canonical SFFI owner.

This removes duplicate boundary declarations and wrapper maintenance without a
runtime call, branch, allocation, GC operation, value clone/free, copy, lookup,
or layout change. A static owner ratchet fixes the canonical inventory at 32
and forbids declarations or wrappers in the compatibility facade; it passed
with the whitespace check.

Estimated declaration rows decrease from 11,713 to 11,681 while symbols remain
3,137. Unsafe-tagged rows remain 1,770, untouched rows decrease from 9,687 to
9,655, and exact-artifact verified-and-signed admission remains zero. The 32
canonical runtime declarations remain the next contract-tagging target.

## Runtime-value raw-contract ownership checkpoint

All 32 declarations in the canonical runtime SFFI owner now carry adjacent,
operation-specific `@unsafe(... capabilities: [ffi])` metadata. The contracts
cover GC initialization/collection/allocation, owned scalar/string/array/dict
value construction, borrowed string pointer/length input, type discriminants
and projections, raw string pointer/out-length projection, clone/free ownership,
arithmetic owned results, comparisons, and value output.

The owner ratchet now requires all 32 canonical declarations to retain their
tags in addition to forbidding duplicate providers in the compatibility
facade. It passed with the whitespace check. This pass changes no ABI signature,
GC operation, allocation, clone/free, arithmetic, comparison, output, branch,
copy, value layout, or dispatch. Production Simple and optimizer verification
remain unavailable.

Estimated totals remain 11,681 declaration rows / 3,137 symbols.
Unsafe-tagged rows increase from 1,770 to 1,802, untouched rows decrease from
9,655 to 9,623, and exact-artifact verified-and-signed admission remains zero.
Allocation failures, projection validity, raw string out-length, and owned
result lifetimes still require executable validation and signed admission.

## System environment/process/time raw-contract checkpoint

All 39 declarations in the canonical system owner now carry adjacent,
operation-specific `@unsafe(... capabilities: [ffi])` metadata. Eight process
contracts were already tagged, and nullable environment lookup already had
recognized contract state; the pass closes the remaining 30 untouched rows.
The contracts cover home/hostname/UUID text, optional environment lookup and
mutation/snapshots, process arguments and IDs, captured execution/spawn/wait/
kill, shell commands, host capability values, wall/monotonic/local time,
timestamp formatting/parsing/differences, and blocking sleep.

A static ratchet fixes the inventory at 39 and requires every declaration to
retain its tag. It passed with the whitespace check. This pass changes no ABI
signature, environment lookup, process/shell operation, capture allocation,
clock query, timestamp parse/format, sleep, branch, copy, or dispatch.
Production Simple and optimizer verification remain unavailable.

Estimated totals remain 11,681 declaration rows / 3,137 symbols.
Unsafe-tagged rows increase from 1,802 to 1,832, untouched rows decrease from
9,623 to 9,593, and exact-artifact verified-and-signed admission remains zero.
Ambiguous empty text and timestamp/host discriminant sentinels still require
typed results and exact provider admission.

## Canonical I/O raw-contract checkpoint

All 34 declarations in the canonical I/O owner now carry adjacent,
operation-specific `@unsafe(... capabilities: [ffi])` metadata. Four nullable
line/mmap/lock contracts already had recognized state; this pass closes the
remaining 30 untouched rows. The contracts cover file metadata, text/byte
reads and writes, atomic/append/copy/move/delete, legacy and SHA-256 hashes,
file locks, mmap text/bytes, directory list/walk/recursive search/mutation, and
path joining/normalization/decomposition.

The metadata identifies ambiguous non-optional empty text/array/hash results
instead of calling them verified success. A static ratchet fixes the inventory
at 34 and requires every declaration to retain its tag; it passed with the
whitespace check. This pass adds no existence check, filesystem operation,
hash pass, lock attempt, mmap operation, recursive scan, path transformation,
allocation, buffer copy, branch, or dispatch. Production Simple and optimizer
verification remain unavailable.

Estimated totals remain 11,681 declaration rows / 3,137 symbols.
Unsafe-tagged rows increase from 1,832 to 1,862, untouched rows decrease from
9,593 to 9,563, and exact-artifact verified-and-signed admission remains zero.
Ambiguous non-optional empty results and lock/mmap sentinels still require typed
contracts and exact provider admission.

## Canonical AST raw-contract checkpoint

The two no-GC sync AST library modules previously carried the same 29 raw
declarations and wrappers. `std.nogc_sync_mut.sffi.ast` is now the sole owner;
the legacy `std.nogc_sync_mut.ffi.ast` module is a zero-cost re-export facade.
All 29 canonical declarations have adjacent, operation-specific
`@unsafe(... capabilities: [ffi])` metadata covering opaque expression,
argument, and node handles; unchecked indexed child access; runtime-owned text;
release operations; and process-global registry invalidation.

The owner ratchet fixes the inventory at 29, requires every canonical
declaration to retain its tag, and rejects foreign declarations in the legacy
facade. This pass changes no ABI signature, registry lookup, AST traversal,
allocation, string copy, release call, branch, or dispatch. The application
interpreter's separate 28-declaration raw facade remains untouched pending an
ownership/import migration. Production Simple and optimizer verification remain
unavailable.

Estimated totals decrease from 11,681 to 11,652 declaration rows while symbols
remain 3,137. Unsafe-tagged rows increase from 1,862 to 1,891, untouched rows
remain 9,563, and exact-artifact verified-and-signed admission remains zero.

The application interpreter's 29 raw declarations are now also explicitly
tagged while its raw-name relative-import API remains intact. The shared AST
ratchet covers both surfaces. No ABI, boolean representation, registry access,
AST traversal, allocation, copy, release, branch, or dispatch changed.
Estimated unsafe-tagged rows increase from 1,891 to 1,920 and untouched rows
decrease from 9,563 to 9,534; signed exact-artifact admission remains zero.

## SQLite legacy raw-contract checkpoint

All 27 `rt_sqlite_*` declarations in each of the canonical no-GC library,
application SFFI, and application FFI surfaces now carry adjacent
operation-specific `unsafe(ffi)` metadata. They remain deliberately unverified:
the native C provider returns nullable tagged handles and integer sentinels,
while the Rust interpreter fabricates zero or empty text for several invalid
handles. In particular, query stepping conflates done with failure; scalar zero
can be a valid value or failure; and column text can represent SQL NULL,
invalid access, or an empty value.

Fixing this requires one status/out v2 contract introduced atomically across C,
Rust interpreter dispatch, and Simple wrappers. A one-lane return change would
create cross-engine ABI divergence. This annotation pass adds no query,
statement step, column read, string conversion, allocation, copy, branch,
lookup, or dispatch. A static ratchet fixes all three inventories at 27 and
keeps the principal ambiguities explicit. The Simple edits are metadata-only,
so optimizer output would not measure a runtime transformation; native runtime
behavior is covered separately below.

Estimated declaration totals remain 11,652 / 3,137 symbols. Unsafe-tagged rows
increase from 1,920 to 2,001, untouched rows decrease from 9,534 to 9,453, and
exact-artifact verified-and-signed admission remains zero.

## Bootstrap synchronization ABI checkpoint

The bootstrap synchronization module's declarations did not match the Rust
runtime: mutex and RwLock constructors omitted their initial `RuntimeValue`,
mutex unlock omitted the replacement value, Once declared an integer return
where the provider returns void/bool, TLS treated `RuntimeValue` as `i64`, and
the wrapper called provider RwLock unlock shims that are explicit no-ops.

The 26 remaining declarations now match those provider shapes and carry
adjacent `unsafe(ffi)` metadata. Mutex callbacks use the value returned while
the provider lock is held and return the retained/updated value on unlock.
RwLock wrappers consume provider snapshots and use `rt_rwlock_set` for updates
instead of pretending a no-op unlock preserves a guard. TLS stores/loads `Any`
directly. `Once.call` invokes its initializer locally rather than passing it to
the provider's non-executing callback stub and silently marking it done.

This does not make the module verified: the RwLock provider drops its guard
before the Simple callback, CondVar wait/timeout are stubs, and local Once state
is not an atomic cross-thread once-cell. Those contracts remain explicitly
unsafe pending a real guard/token design. The changes add no steady-state
allocation, registry lookup, lock, sleep, spin, copy, or generic dispatch; they
remove two no-op calls and one non-executing callback-provider call.

A static ABI/contract ratchet fixes these signatures and forbids restoration of
the no-op unlock surface. Estimated declarations decrease from 11,652 to 11,651
while symbols remain 3,137. Unsafe-tagged rows increase from 2,128 to 2,154,
untouched rows decrease from 9,326 to 9,302, and exact-artifact signed admission
remains zero.

## Simple-core array raw-contract checkpoint

All 24 allocator, memory, archive-level array, registry, and runtime-array
externs in `core_array_ops.spl` now carry adjacent `unsafe(ffi)` metadata, with
`raw_ptr` capability where raw allocation/header/item addresses cross the
boundary. This includes extent-sensitive loads, stores, and `memcpy`, registry
publication/invalidation, and allocation/status sentinels.

One concrete leak is fixed: if the u64 array header allocation succeeds but its
item allocation fails, the header is now freed before returning failure. A
constant-time upper bound prevents `capacity * 8` overflow, and concatenation
rejects signed length overflow before allocating. These add only failure-path
cleanup and two O(1) guards—no traversal, copy, allocation, registry lookup, or
dispatch. A static ratchet fixes the inventory and cleanup/overflow invariants.
The focused `bin/simple check` completed, but that command identified its binary
as the Rust bootstrap seed; it is recorded only as limited syntax evidence, not
production verification. The Pure Simple optimizer was therefore not replaced
with the seed and remains unavailable for this checkpoint.

Estimated declaration totals remain 11,652 / 3,137 symbols. Unsafe-tagged rows
increase from 2,104 to 2,128, untouched rows decrease from 9,350 to 9,326, and
exact-artifact verified-and-signed admission remains zero.

## FTP/FTPS unbacked-boundary checkpoint

The canonical FTP owner has 25 raw declarations and no C or Rust provider or
interpreter registration in the current tree. Application and GC variants are
already compile-time re-export facades. The LLM Caret storage selector detects
this state and rejects FTP before invoking the boundary instead of accepting a
fabricated handle.

All 25 declarations now carry adjacent operation-specific `unsafe(ffi)`
metadata covering connection ownership, credentials, TLS policy, remote/local
paths, transfers, ambiguous empty text, negative size failure, transfer modes,
and keep-alive state. A static ratchet requires those tags, rejects appearance
of an unreviewed runtime/interpreter provider, and preserves the storage
fail-closed guard. This metadata adds no network/file operation, allocation,
copy, lookup, lock, branch, or dispatch.

Estimated declaration totals remain 11,652 / 3,137 symbols. Unsafe-tagged rows
increase from 2,079 to 2,104, untouched rows decrease from 9,375 to 9,350, and
exact-artifact verified-and-signed admission remains zero.

The native C provider now rejects non-heap scalar values before pointer
untagging on every connection/statement operation, and `close(nil)` no longer
fabricates success. This is an O(1) bit-tag branch with no registry or
allocation. It cannot distinguish a stale or wrong-kind heap object, so the
boundary remains unsafe pending generation-checked typed handles. Transaction
begin/commit/rollback now execute static C literals directly instead of
allocating and copying a temporary runtime string on every call. Strict C11
`-Wall -Wextra -Werror` syntax lint and Clang static analysis completed without
diagnostics; these checks do not constitute artifact signing or formal proof.

The existing ACID probe then passed all eight focused transaction stages across
memory and file databases, including non-vacuous inserts and rollback recovery.
Its later native enterprise-store compilation failed because 14 closure
functions still require the interpreter. That blocker is recorded in
`doc/08_tracking/bug/sqlite_acid_native_store_closure_blocked_2026-08-25.md`;
the overall gate is therefore FAIL, not verified, and was not rerun.

## HTTP and WebSocket legacy raw-contract checkpoint

All 26 HTTP/WebSocket declarations in each of the no-GC library, application
SFFI, and application FFI facades now carry adjacent operation-specific
`unsafe(ffi)` metadata. The contracts cover runtime-owned response tuples,
transport-failure status, generation-encoded client handles, raw server and
WebSocket handles, header arrays, filesystem download/upload paths, and the
ambiguous empty-text WebSocket receive result.

This is metadata only: it adds no DNS query, connection, request, response read,
file operation, allocation, copy, lock, handle lookup, branch, or dispatch, and
preserves native boolean ABIs. The existing provider surface remains incomplete
across lanes and is neither signed nor semantically verified. A static ratchet
fixes each facade at 26 declarations.

Estimated declaration totals remain 11,652 / 3,137 symbols. Unsafe-tagged rows
increase from 2,001 to 2,079, untouched rows decrease from 9,453 to 9,375, and
exact-artifact verified-and-signed admission remains zero.

## Compression and archive raw-contract checkpoint

The no-GC compression facade owns 24 raw gzip, deflate, zip, tar, and tar.gz
declarations. No matching non-vendored C or Rust provider exists in the
repository. All 24 declarations now carry adjacent operation-specific
`unsafe(ffi)` metadata. The reasons preserve the unresolved obligations:
binary bytes are represented as `text`, allocation and output extents are
unknown, empty text conflates valid empty output with failure, integer handles
lack typed ownership/generation, and extraction has no reviewable traversal,
link, overwrite, or expansion-limit policy.

No public API, boolean result, call, branch, allocation, copy, lookup, lock, or
dispatch changed. Adding speculative validation in the safe-looking facade
would not establish provider behavior and could add hot-path work, so the lane
remains explicitly unsafe pending a typed provider contract. A static ratchet
requires all 24 tags and rejects the appearance of an unreviewed provider.

Estimated repository totals are 11,651 declarations / 3,137 symbols.
Unsafe-tagged rows increase from 2,202 to 2,226, untouched rows decrease from
9,254 to 9,230, and exact-artifact verified-and-signed admission remains zero.

## SSH and SFTP raw-contract checkpoint

The canonical no-GC SSH facade owns 23 raw SSH/SFTP declarations; the other
memory/concurrency families and application module are compatibility facades.
No matching transport provider exists in non-vendored runtime C or Rust code.
All 23 declarations now carry adjacent operation-specific `unsafe(ffi)`
metadata, and the stale comment claiming 30 declarations is corrected.

Unresolved obligations include host-key and TLS-equivalent transport policy,
credential/passphrase lifetime, generation-checked session/channel/SFTP
handles, command output bounds, binary channel extents and partial writes,
remote/local path validation, destructive SFTP operations, metadata failure
encoding, and empty-versus-EOF/failure text results. The unrelated in-tree SSH
AES and authentication-test helpers are not providers for this facade.

This is metadata only: it adds no connection, authentication, command, read,
write, transfer, filesystem access, allocation, copy, lookup, lock, branch, or
dispatch. A static ratchet requires all 23 tags and rejects appearance of an
unreviewed provider.

Estimated repository totals remain 11,651 declarations / 3,137 symbols.
Unsafe-tagged rows increase from 2,226 to 2,249, untouched rows decrease from
9,230 to 9,207, and exact-artifact verified-and-signed admission remains zero.

## Process I/O raw-contract checkpoint

The canonical no-GC process owner has 23 declarations and the application
closure owner has 15. The final six and five untagged declarations respectively
now carry `unsafe(ffi)` metadata, and every direct call added by those legacy
declarations is lexically scoped. Browser renderer sandbox spawn/enter still
have no C or Rust provider. File read exists but returns nullable
`RuntimeValue` while both legacy facades declare non-optional `text`. Native
stderr write and flush providers return `i64` status while these facades discard
it through unit declarations; the providers also currently return zero even
when Rust flush reports failure.

The lexical/metadata changes add no syscall, filesystem access, process launch,
poll, allocation, copy, lookup, lock, branch, or generic dispatch. Variable
placement around lexical unsafe regions retains the same single file-size/read
or flush operation per existing loop iteration. A static ratchet fixes both
inventories, requires every tag, rejects an unreviewed browser provider, and
pins the known native signatures until one canonical generated contract
replaces duplicate declarations.

Estimated repository totals remain 11,651 declarations / 3,137 symbols.
Unsafe-tagged rows increase from 2,249 to 2,260, untouched rows decrease from
9,207 to 9,196, and exact-artifact verified-and-signed admission remains zero.

## Shared I/O runtime raw-contract checkpoint

The shared no-GC I/O owner has 37 raw declarations. Its final 18 untagged file,
directory, platform, clock, hash, exit, and shell declarations now carry
operation-specific `unsafe(ffi)` metadata and their direct calls are lexically
scoped. Provider inspection confirmed that raw byte reads, directory lists,
and platform names can return `nil`; those raw declarations are now optional,
while their existing public APIs retain the intended `[]` or `"unknown"`
fallback. This fixes the type contract without an additional provider call,
scan, allocation, or copy.

Remaining unverified semantics include Boolean I/O failure conflation,
recursive-delete policy, empty recursive-walk failure, shell output/status
ambiguity, runtime hash stability, clock failure, and array ownership. The
Rust native `rt_exit` accepts `i32` and never returns, while simple-core accepts
`i64` and returns `i64`; the audit pins this cross-lane ABI conflict pending
generated typed thunks. `rt_shell_exec` remains interpreter-only rather than a
native provider.

All added unsafe regions are compile-time structure. Existing wrappers retain
one provider invocation and their previous algorithms; no filesystem call,
directory traversal, shell launch, allocation, copy, lookup, lock, or generic
dispatch was added.

Estimated repository totals remain 11,651 declarations / 3,137 symbols.
Unsafe-tagged rows increase from 2,260 to 2,278, untouched rows decrease from
9,196 to 9,178, and exact-artifact verified-and-signed admission remains zero.

## Atomic raw-contract and Boolean RMW checkpoint

The canonical no-GC atomic facade had 16 untagged raw declarations and exposed
four safe-looking Boolean read-modify-write methods implemented as separate
load/swap/store calls. `compare_exchange` could swap a value and then overwrite
a concurrent writer while compensating for mismatch; Boolean and/or/not had
the same non-atomic load/store race. The hosted Rust provider now exports four
typed Boolean RMW primitives, and interpreter registration plus native ABI
metadata use the same signatures. The Simple methods each make one direct
foreign call, so compare-exchange drops from as many as three provider calls
to one and Boolean bitwise RMW drops from two calls to one.

All 20 raw atomic declarations are explicitly `unsafe(ffi)` and every call is
lexically scoped. The public Boolean API and true/false types are preserved.
No allocation, copy, retry loop, extra memory ordering fence, registry lookup,
lock, or dispatch was added per call; the corrected operations reduce existing
global-map mutex acquisitions.

Factory wrappers now reject a non-positive allocation handle once, outside the
operation hot path. Manual `free` methods are explicitly unsafe because the
legacy class cannot consume itself or invalidate its private handle; callers
must prevent use-after-free and duplicate release. Ordinary load/store/RMW
methods remain safe only for live objects produced by the checked factories.

This does not make the atomic provider safe. Hosted operations still acquire a
global `Mutex<HashMap>` despite the facade's lock-free claim, use `SeqCst`
regardless of requested ordering, and fabricate zero/false or discard writes
for stale/invalid handles. The simple-core fallback implements only a partial,
single-threaded pointer-backed integer subset. Typed generation-checked direct
slots and ordered thunks remain required before verified admission.

The GC async atomic module was a full duplicate owner with the old multi-call
Boolean implementation and 16 additional untagged declarations. It is now a
zero-runtime-cost compatibility facade over the canonical no-GC sync owner,
matching the existing no-GC async family structure and removing that divergent
unsafe surface.

Estimated repository totals decrease to 11,639 declarations / 3,141 symbols.
Unsafe-tagged rows increase from 2,278 to 2,298, untouched rows decrease from
9,178 to 9,162, and exact-artifact verified-and-signed admission remains zero.

Focused evidence: the direct Boolean RMW truth-table test passed; an eight-
thread contention test proved exactly one successful false-to-true CAS; and
`cargo check -p simple-compiler` completed with four pre-existing unrelated
warnings. The atomic static contract audit passed. These results validate the
Rust provider and registration edits, but they are not signed exact-artifact or
cross-engine production-Simple evidence.

## Fast in-memory database raw-contract checkpoint

The specialized `FastTable` accelerator owns 21 `rt_db_*` declarations backed
by native C and a separate Rust interpreter implementation. It is not the
general embedded-database default; ordinary Simple code should continue to use
PureDatabase. All 21 declarations now carry explicit `unsafe(ffi)` contracts,
all calls are lexically scoped, creation rejects a negative provider handle,
manual destruction is explicitly unsafe, and the nullable managed-text result
is represented as `text?`. Legacy methods remain explicitly unsafe
because zero, empty, default, and `-1` still conflate valid data, absence,
invalid handles, allocation failure, and provider failure.

The C provider no longer casts the three integer batch values to pointers when
a legacy text-mask bit is set; nonzero masks fail closed. Allocation and growth
paths now check overflow/failure and publish replacements only after success.
Text-to-integer updates release retained text storage, and integer primary keys
use `PRId64` so Windows does not truncate them through 32-bit `long`.

The integer hot path remains O(1) average indexed access. It gains no per-call
hash/signature verification, dynamic symbol lookup, lock, generic dispatch, or
copy; the three-value loop loses its text-mask branch. Allocation checks occur
only on existing allocation/growth paths. Native syntax checking and the static
contract audit cover these edits, but they are not proof, cross-engine evidence,
or signed exact-artifact admission. The generationless 64-slot global registry
is unsynchronized and the Rust interpreter contract remains independently
implemented, so this family is not safe or verified.

Estimated repository totals remain 11,639 declarations / 3,141 symbols.
Unsafe-tagged rows increase from 2,298 to 2,319, untouched rows decrease from
9,162 to 9,141, and exact-artifact verified-and-signed admission remains zero.

## oneAPI partial-provider raw-contract checkpoint

The canonical oneAPI facade declares 24 `rt_oneapi_*` operations. Native C,
the seed-only C satellite, and the Rust interpreter dispatcher expose only the
same 14 symbols, all fixed capability-unavailable stubs; device metadata and
selection, shared allocation, both copies, global synchronization, and error
text are unbacked. The Rust dispatcher incorrectly described the partial stub
ABI as the full family and accepts only integer values even where the Simple
surface declares text or byte arrays. This is neither a real oneAPI provider
nor cross-lane typed evidence.

All 24 declarations now carry operation-specific `unsafe(ffi)` metadata, with
`raw_ptr` on allocation, span, module, kernel, and queue operations. Every raw
call is lexically scoped. Invalid pointer/module/queue wrappers now return
`false` instead of fabricating successful release or wait. Host-data allocation
now observes copy failure, releases the allocation on that error path, and
returns an invalid value instead of reporting a populated device allocation.

No successful allocation, copy, compile, lookup, launch, wait, or release path
gains hashing, signature verification, provider discovery, dynamic lookup,
allocation, copying, locking, or generic dispatch. The host-data helper gains
one required status branch and cleanup only when its existing transfer fails.
Exact signed provider admission remains zero, and this family stays unverified
until a real provider, typed generated registry, ownership/generation model,
and cross-lane tests replace the handwritten partial stubs.

Estimated repository totals remain 11,639 declarations / 3,141 symbols.
Unsafe-tagged rows increase from 2,319 to 2,343, untouched rows decrease from
9,141 to 9,117, and exact-artifact verified-and-signed admission remains zero.

## Legacy CUDA I/O raw-contract and ABI-collision checkpoint

The 23-declaration CUDA I/O convenience facade is not the canonical low-level
CUDA owner. Provider inspection found 16 declared names with no owned runtime
definition. Of the remaining shared names, `rt_cuda_launch_kernel` collides
with the canonical module/name/status ABI while this facade declares a function
handle/argument-array/Boolean ABI; `rt_cuda_memset` similarly disagrees on
Boolean versus integer status. A linker can therefore resolve the right name
to the wrong calling contract. Unsafe metadata cannot repair that collision.

All 23 raw declarations now carry operation-specific `unsafe(ffi)` metadata,
including `raw_ptr` for memory, module, function, stream, and launch contracts.
Every raw call is lexically scoped. Invalid release/synchronization no longer
fabricates success. Copy wrappers check known allocation extents, allocation
rejects non-positive sizes before entering the provider, and launch geometry
rejects invalid dimensions. One-dimensional grid rounding no longer risks
signed overflow or division by zero. Host-data allocation observes transfer
failure, releases on that error path, and returns invalid.

These checks are constant-time and add no provider invocation, allocation,
copy, lookup, lock, hashing, signing, or generic dispatch. Valid transfers and
launches gain only contract-required scalar comparisons; invalid inputs avoid
foreign work, and failed host transfer alone gains cleanup. The facade remains
unverified and unsafe pending removal or uniquely named generated contracts;
exact-artifact verified-and-signed admission remains zero.

Estimated repository totals remain 11,639 declarations / 3,141 symbols.
Unsafe-tagged rows increase from 2,343 to 2,366, untouched rows decrease from
9,117 to 9,094, and exact-artifact verified-and-signed admission remains zero.

## Engine2D CUDA dynamic-contract checkpoint

The Engine2D CUDA facade owns 23 static declarations and an optional dynamic
driver path. All declarations now carry explicit `unsafe(ffi)` metadata, with
`raw_ptr` for contexts, modules, device memory, argument packs, launches, and
pixel spans. Every static call is lexically scoped and the facade class itself
is unsafe because generationless handles and generic dynamic calls cannot
establish its public invariants.

The dynamic path previously called `cuInit` with no flags argument and treated
the status return of `cuDeviceGetCount`, `cuCtxCreate`, and `cuMemAlloc` as the
requested count/context/pointer even though those APIs return data through out
pointers. Availability now uses `cuInit(0)` and confirms a typed device count;
the three out-parameter operations use their typed static thunks until typed
dynamic thunks exist. Dynamic shutdown no longer fabricates success for an API
the lane cannot perform. Six declared shutdown/argument-pack/pixel-helper
symbols remain wholly unbacked and are pinned by the audit.

Pixel helper wrappers reject invalid handles, negative/misaligned byte extents,
and spans shorter than the requested transfer before entering foreign code.
Context, module, kernel, memory, and launch wrappers reject invalid scalar
contracts in constant time. No valid launch or transfer gains another provider
call, allocation, copy, lock, hash, signature operation, lookup, or generic
dispatch; incorrect dynamic out-parameter calls are removed. This family is
still unsafe and unsigned pending typed provider admission and removal or
implementation of the six missing symbols.

Estimated repository totals remain 11,639 declarations / 3,141 symbols.
Unsafe-tagged rows increase from 2,366 to 2,389, untouched rows decrease from
9,094 to 9,071, and exact-artifact verified-and-signed admission remains zero.

## `CudaDynFfi` authority-reduction checkpoint

The second Engine2D CUDA facade declared 21 static hooks. Twelve were unused,
unbacked helpers/aliases, or an ABI-incompatible function-handle declaration
under the canonical module/name `rt_cuda_launch_kernel` symbol. The facade now
retains only nine provider-backed declarations, all explicitly `unsafe(ffi)`
and lexically scoped. The class itself remains unsafe because dynamic symbol
identity, handle generations, ownership, and pointer arguments are unproved.

Static PTX loading, function lookup, and synchronization now use the canonical
`rt_cuda_module_load_data`, `rt_cuda_module_get_function`, and `rt_cuda_sync`
identities. No exact static function-handle launch provider exists, so that
branch fails closed instead of invoking the canonical symbol with shifted
arguments and undefined behavior. Dynamic mode retains its one direct
`cuLaunchKernel` call. Legacy shutdown also returns failure rather than claiming
an operation that the facade cannot perform.

Scalar guards reject invalid device, module, function, allocation, geometry,
and shared-memory inputs before foreign execution. Generic dynamic dispatch is
still prohibited for device count, context creation, and memory allocation
because those CUDA APIs return through out pointers. Valid dynamic launch and
typed static calls gain no allocation, copy, lookup beyond the already selected
symbol, lock, hash, signing work, provider call, or adapter layer.

Estimated repository totals decrease to 11,627 declarations / 3,141 symbols.
Unsafe-tagged rows increase from 2,389 to 2,398, untouched rows decrease from
9,071 to 9,050, and exact-artifact verified-and-signed admission remains zero.

## ROCm I/O raw-contract checkpoint

The ROCm I/O facade's 23 declarations are backed by a real optional Linux C
provider that loads HIP/HIPRTC once and caches typed function pointers. The
Rust interpreter lane is not that provider: it is a fixed unavailable
simulation returning false, zero, `-3`, and empty text. Source presence and
registration therefore do not establish cross-lane semantic verification.

All 23 declarations now carry operation-specific `unsafe(ffi)` metadata, with
`raw_ptr` for memory, module, function, stream, span, and launch operations.
Every raw call is lexically scoped. Device-name and last-error managed-text
returns are nullable at the raw boundary; their existing nonoptional public
APIs fail closed if runtime allocation returns nil rather than fabricating
text. Invalid release/wait no longer reports success.

Allocation rejects non-positive extents. Host/device/device copies validate
known allocation sizes, launch validates positive geometry and shared memory,
and one-dimensional grid rounding avoids overflow and division by zero. A
failed host-data transfer releases its allocation and returns invalid. These
are constant-time checks; successful calls add no provider invocation,
allocation, staging buffer, copy, lookup, lock, hash, signature operation, or
generic dispatch. The provider's existing array-layout staging and per-launch
argument allocations remain a performance/ownership verification obligation,
not a regression introduced here.

Estimated repository totals remain 11,627 declarations / 3,141 symbols.
Unsafe-tagged rows increase from 2,398 to 2,421, untouched rows decrease from
9,050 to 9,027, and exact-artifact verified-and-signed admission remains zero.

## SDL3 I/O raw-contract checkpoint

The SDL3 facade has 22 Simple declarations backed by the optional C provider
and a family-specific Rust interpreter dispatcher. All declarations now carry
operation-specific `unsafe(ffi)` metadata and every raw call is lexically
scoped. Event-text and error-text lifts are nullable at the raw boundary; the
public wrapper returns a backend error or panics with a stable SFFI diagnostic
when the lift fails instead of fabricating empty text.

The interpreter continues to use typed C signatures and rejects null C text.
Its library handle was already cached, but every event accessor still repeated
`dlsym`. A fixed 24-slot atomic symbol cache now resolves each address once,
without a mutex, map, allocation, or per-call ownership copy. The scalar event
path otherwise retains the same provider-call count and constant-space data
flow. Text events retain their existing single managed-text allocation.

This establishes source-level unsafe authority, provider/registry coverage,
null rejection, and a static contract ratchet. It does not authenticate the
SDL3 library or bind it to signed evidence; provider state is also process
global and remains unsafe. Estimated repository totals remain 11,627
declarations / 3,141 symbols. Unsafe-tagged rows increase from 2,421 to 2,443,
untouched rows decrease from 9,027 to 9,005, and exact-artifact
verified-and-signed admission remains zero.

## Shared GPU foreign-text null checkpoint

The Rust interpreter GPU adapter used one shared `c_ptr_to_string` lift for
Metal device/error text and feature-enabled CUDA device/error text. A null
provider pointer was converted to `String::new()`, fabricating valid empty text
where the foreign contract had failed. The lift now returns a typed runtime
error naming the symbol; all four callers propagate it.

The success path retains the same single C-string scan and owned-string
allocation. The only added work is the required null comparison, with no extra
provider call, copy, lookup, lock, hash, signing operation, or dispatch.
`metal-sffi-symbol-identity.shs` passes and pins the non-fabrication rule. The
focused Rust test passed (1 test, zero failures; 3,928 unrelated compiler tests
filtered out).

This fixes one shared lifting defect but does not yet scope the 67 raw Metal
calls in the Simple facade or authenticate the provider. Census and declaration
counts are unchanged; exact-artifact verified-and-signed admission remains
zero.

## SDL2 event-consumer authority checkpoint

The canonical SDL2 facade already tagged its 65 raw declarations, but two
production consumers bypassed its lexical boundary for 29 cached-event reads:
the web UI translator and hosted compositor input backend. Each read is now
inside a minimal `unsafe(ffi)` scope. Safe state updates, event construction,
button interpretation, and key translation remain outside those scopes.

The event-family audit now covers both consumers as well as the provider. It
pins the cached detail accessors as O(1), allocation-free, lock-free, and free
of an extra poll. No event gains a provider call, allocation, ownership copy,
lookup, lock, hash, signature operation, or dispatch layer.

The same source census before and after the edit measured the SDL2 family
moving from 107 explicit / 29 missing authority call sites to 136 explicit /
zero missing. Repository-wide missing authority fell from 18,339 to 18,310;
production missing authority fell from 10,169 to 10,140. Declaration totals
remain 11,627, with 2,443 unsafe-tagged and 9,005 untouched declaration rows.
Exact-artifact verified-and-signed admission remains zero.

## Canonical Metal facade authority checkpoint

The canonical Metal file's 40 declarations were already tagged, but its 67
production raw calls lacked authority. Typed public wrappers now confine FFI
to lexical blocks. The lower `metal_sffi_*` surface remains explicitly unsafe
at function scope because it exposes generationless device, buffer, shader,
pipeline, queue, command, encoder, and pointer-bearing frame contracts.

Invalid release and wait wrappers no longer manufacture success. Allocation
rejects non-positive extents, texture creation rejects non-positive geometry,
and uploads/downloads reject a span larger than the recorded buffer extent.
Quarantine cleanup preserves dependencies unless wait or registry removal
proves terminal ownership, as before.

The authority scopes and scalar guards add no provider invocation, allocation,
copy, lookup, lock, hash, signature operation, or dispatch. Successful GPU
operations keep their existing direct call shape. The source census measured
missing authority decreasing by exactly 67: 18,274 to 18,207 repository-wide
and 10,104 to 10,037 in production (35 new lexical and 32 function-scoped
authorities). Declaration totals remain 11,627, with 2,449 tagged and 8,999
untouched; exact-artifact verified-and-signed admission remains zero.

## TCP byte-write consumer checkpoint

Two duplicate TCP consumers bypassed the canonical facade's authority: SSH
client transport called `rt_io_tcp_write`, and the async driver called
`rt_io_tcp_write_bytes`. Both declarations and calls now use minimal lexical
`unsafe(ffi)` scopes. The SSH adapter rejects invalid descriptors, zero
progress for nonempty input, and provider counts larger than the borrowed
slice before advancing its send cursor.

The native C provider remains a direct descriptor/array validation followed
by one `write(2)` call; the interpreter uses its typed network registration.
No provider call, allocation, copy, lookup, lock, hash, signature operation,
or dispatch layer was added. The existing SSH suffix slicing remains a known
copying cost and is not claimed verified by this authority change.

The source census measured missing authority decreasing from 18,276 to 18,274
repository-wide and from 10,106 to 10,104 in production. `rt_io` now has 315
explicit and 25 missing call sites. Declaration totals remain 11,627;
unsafe-tagged declarations increase from 2,447 to 2,449 and untouched
declarations decrease from 9,001 to 8,999. Exact-artifact
verified-and-signed admission remains zero.

## Synchronous file I/O raw-contract checkpoint

The canonical `FileHandle`/`File` facade has 16 explicitly unsafe declarations
backed by both typed interpreter registrations and a native Rust C ABI. Its 20
production raw calls were outside lexical authority; each is now scoped to the
exact provider operation. Negative read extents are rejected before crossing
the boundary.

Provider review found that both write functions passed `(null, 0)` to Rust's
`slice::from_raw_parts`, which is undefined behavior even for an empty slice.
Zero-length writes now use `&[]`; nonempty writes validate both pointer and
target `usize` extent. Bounded reads replace infallible `vec![0; size]` with
checked conversion and fallible exact reservation, returning the existing nil
failure sentinel rather than aborting on capacity failure.

Valid reads retain one buffer allocation and one read; valid writes retain one
write call and no new allocation or copy. No lookup, lock, hash, signing work,
or generic dispatch was added. The Rust provider still accepts generationless
raw file descriptors, `read_all` remains caller-unbounded, and boolean
exists/delete results cannot distinguish false from provider failure, so this
family remains unsafe and unsigned.

The source census measured repository-wide missing authority decreasing from
18,310 to 18,290 and production missing authority from 10,140 to 10,120. The
broader `rt_io` family now has 306 explicit and 34 missing call sites.
Declaration totals remain 11,627, with 2,443 unsafe-tagged and 9,005 untouched
rows; exact-artifact verified-and-signed admission remains zero.

Focused Rust provider verification passed: 81 `file_io`-filtered tests, zero
failures (1.01 seconds; 1,146 unrelated tests filtered out).

## Aspect-pack I/O authority and overflow checkpoint

The compiler aspect-pack loader had four tagged file calls but also four
untagged mmap, unmap, raw-pointer-read, and file-size declarations. All eight
declarations and their 14 production call sites now carry minimal lexical FFI
authority; pointer operations additionally require `raw_ptr`.

Both mapping and positioned-read EOF checks previously formed
`offset + length` on attacker-controlled geometry before comparing it with the
file size. They now use subtraction after validating positive bounded length,
so signed overflow cannot turn an out-of-file range into an admitted one. The
existing 64 MiB materialization cap, aligned mapping arithmetic, one
open/map/close sequence, and one open/seek/read/close sequence are unchanged.
The per-byte mapped copy gains only compile-time authority metadata: no extra
call, allocation, copy, branch, lookup, lock, hash, or signing operation.

The source census measured repository-wide missing authority decreasing from
18,290 to 18,276 and production missing authority from 10,120 to 10,106. The
broader `rt_io` family now has 313 explicit and 27 missing call sites.
Declaration totals remain 11,627; unsafe-tagged declarations increase from
2,443 to 2,447 and untouched declarations decrease from 9,005 to 9,001.
Exact-artifact verified-and-signed admission remains zero.

## Engine2D Vulkan raw-facade authority checkpoint

The Engine2D Vulkan owner has 59 already-tagged declarations and 90 production
calls that were previously treated as safe. Its ABI selectors, dual-dispatch
class methods, generationless handle/resource façades, quarantine ownership,
presentation operations, and headless device selection are now explicitly
unsafe at their narrow function boundaries. The checked compute orchestrator
also remains unsafe because scalar validation cannot prove foreign handle
generation, aliasing, or provider identity.

No generic Vulkan driver calls were introduced. Dynamic mode retains exactly
one `vkEnumerateInstanceVersion` loader probe and rejects operational dispatch;
static mode keeps direct typed thunks. Existing region and strided-copy bounds
remain capped and overflow-safe. Authority metadata adds no provider call,
allocation, copy, lookup, lock, hash, signature work, branch, or dispatch.

The source census measured missing authority decreasing by exactly 90: 18,207
to 18,117 repository-wide and 10,037 to 9,947 in production. All 90 became
function-scoped authorities. Declaration totals remain 11,627, with 2,449
tagged and 8,999 untouched; exact-artifact verified-and-signed admission
remains zero.

## Engine2D Vulkan alias-facade authority checkpoint

The sibling `ffi_vulkan.spl` module is an alias facade over the canonical
`rt_vulkan_*` ABI rather than a separate provider. Its 48 production calls now
carry function-scoped FFI authority across the raw `VulkanDynFfi` methods and
the global `vulkan_ffi_*` compatibility entry points. These APIs remain unsafe
because they expose generationless raw handles and cannot establish provider
identity, object lifetime, or aliasing from their scalar inputs.

Dynamic mode remains resolve-only: it looks up
`vkEnumerateInstanceVersion` but does not invoke an operational generic
dispatcher. Static mode continues to call the existing typed canonical
thunks. The annotations add no provider call, allocation, copy, lookup, lock,
hash, signing work, runtime branch, or dispatch overhead.

The source census measured missing authority decreasing by exactly 48: 18,117
to 18,069 repository-wide and 9,947 to 9,899 in production. All 48 became
function-scoped authorities. The broader `rt_vulkan` family now has 134
explicit and 324 missing call sites. Declaration totals remain 11,627, with
2,449 tagged and 8,999 untouched; exact-artifact verified-and-signed admission
remains zero.

## Lyon graphics capability-gap checkpoint

The Lyon graphics module declares 49 raw `rt_lyon_*` functions, but repository
search and the interpreter's capability-gap registry confirm that no native C
or Rust provider exists in tree. Consequently none of its resource handles,
tuples, arrays, text, or boolean results can be promoted to a verified safe
contract. All 49 production wrappers that cross this boundary are now
explicitly function-unsafe, and the negative capability-gap fixture uses a
narrow lexical FFI scope. Invalid resource cleanup now returns `false` instead
of fabricating successful release.

This is authority metadata plus seven fail-closed constant changes on invalid
inputs. Valid paths retain the same direct call, branches, data layout, and
allocations; no provider call, copy, lookup, lock, hash, signing operation, or
dispatch was added. The existing polygon flattening and stroke-options text
construction are unchanged. The identity-only path-transform workaround is
not made safe by this change and remains behind the unsafe boundary.

The source census measured production missing authority decreasing by exactly
49, from 9,899 to 9,850. Including the negative fixture, repository-wide
missing authority decreases by exactly 50, from 18,069 to 18,019: 49 calls
became function-scoped and one became lexically scoped. The `rt_lyon` family
therefore has 50 explicit and zero missing call sites. The fixture adds one
unsafe-tagged declaration; production declaration counts are unchanged.
Exact-artifact verified-and-signed admission remains zero.

## Rapier2D interpreter-provider checkpoint

Rapier2D has 48 tagged raw declarations and an interpreter implementation, but
no matching native C/Rust artifact provider was found outside the interpreter.
All 48 production raw calls, contained in 41 wrapper functions, now carry
function-scoped FFI authority. Three convenience wrappers that delegate to
those functions also propagate the same authority. The facade remains unsafe
because its integer handles have no provider generation, ownership proof, or
signed ABI identity.

Provider review found that ray casting, every joint operation, and joint
counting returned plausible false/zero values despite being unimplemented.
Missing body getters and missing contact records likewise returned valid-looking
zero tuples. These paths now return typed interpreter runtime errors and retain
the last-error diagnostic. Removing an unknown world returns semantic `false`,
and five invalid facade cleanup paths no longer fabricate `true`.

Successful operations retain their existing `HashMap`/mutex access, algorithms,
and allocations. No lookup, lock, copy, hash, signing operation, or dispatch
was added. Diagnostic formatting and allocation occur only on newly fail-closed
error paths. The existing physics-step body-ID vector and contact computation
were not changed or made more expensive.

The source census measured missing authority decreasing by exactly 48: 18,019
to 17,971 repository-wide and 9,850 to 9,802 in production. All 48 became
function-scoped authorities; the `rt_rapier2d` family now has 48 explicit and
zero missing call sites. Focused Rust verification passed four fail-closed
provider tests with zero failures. Exact-artifact verified-and-signed admission
remains zero.

## GPU physics CUDA solver authority checkpoint

The GPU physics solver privately redeclared 12 `rt_cuda_*` operations without
unsafe metadata and invoked them 55 times across compilation, device-buffer
growth, upload, kernel dispatch, download, and destruction. The declarations
and nine raw-calling methods now carry FFI authority; the single top-level
`solve` method propagates that authority because it orchestrates those raw
methods. Pure-Simple spatial hashing, graph coloring, SoA storage, and PTX
kernel material remain unchanged.

This checkpoint is compile-time authority metadata only. It adds no runtime
branch, call, allocation, copy, lookup, lock, hash, signing operation, or
dispatch, and does not change kernel batching or buffer reuse. Review also
found that transfer, launch, synchronization, unload, and free booleans are
ignored, allocation failure can lose capacity truth, and repeated destruction
does not clear every buffer handle. Those are retained as explicit unsafe
obligations rather than being mislabeled verified; they require a separate
fail-closed state-machine patch with measured hot-path evidence.

Provider identity review then found that seven declared names have no runtime
or interpreter implementation: `rt_cuda_memcpy_h2d`, `rt_cuda_memcpy_d2h`,
`rt_cuda_compile_ptx`, `rt_cuda_get_function`, `rt_cuda_synchronize`,
`rt_cuda_stream_create`, and `rt_cuda_stream_destroy`. The declared
`rt_cuda_launch_kernel` ABI is also incompatible with the canonical runtime:
the solver supplies a function handle plus a Simple array and expects `bool`,
whereas the runtime takes a module, length-tracked function name, raw argument
pointer, and returns an integer status. Boolean cleanup cannot repair this ABI
mismatch. The solver must remain unavailable/unsafe until it is regenerated
against the canonical typed CUDA registry; no generic compatibility dispatcher
or numeric coercion should be introduced.

The source census measured missing authority decreasing by exactly 55: 17,971
to 17,916 repository-wide and 9,802 to 9,747 in production. All 55 became
function-scoped authorities. The broader `rt_cuda` family now has 109 explicit
and 337 missing call sites. Twelve declaration rows moved from untouched to
unsafe-tagged. Exact-artifact verified-and-signed admission remains zero.

## Host Vulkan/lavapipe evidence-provider checkpoint

The host lavapipe counterpart exposes two public functions that mutate the
process-global Vulkan ICD selection and directly drive an unsigned Vulkan
provider. Both entries are now explicitly FFI-unsafe. Their 62 previously
unscoped calls became function-scoped; ten newly added calls are also inside
that authority boundary.

The clear/readback path previously multiplied unchecked dimensions, allocated
an unbounded byte array, indexed the first four bytes even when geometry could
produce fewer, accepted a failed depth-image creation, and leaked every valid
depth image. O(1) preflight checks now require positive dimensions no larger
than 8192 per axis and RGBA8 channels in 0..255, capping readback allocation at
256 MiB without overflow. Depth creation fails closed, and six post-creation
cleanup paths release the depth image. The other four new calls provide the
new depth-failure cleanup and diagnostic.

The render/submit/readback hot sequence, pixel-loop complexity, and existing
allocation/copy count are unchanged. No lookup, lock, hash, signing operation,
generic dispatch, or successful-path allocation was added. Cleanup gains one
required destroy call and removes a device-memory leak.

Because ten contract/cleanup calls were added, production raw-call inventory
increased from 12,803 to 12,813 while missing authority still decreased by
exactly 62: 17,916 to 17,854 repository-wide and 9,747 to 9,685 in production.
All 72 calls in the two provider entries are function-scoped. The broader
`rt_vulkan` family now has 206 explicit and 262 missing call sites.
Exact-artifact verified-and-signed admission remains zero.

## VulkanBackend3D lexical-boundary checkpoint

`VulkanRenderBackend3D` implements the ordinary `RenderBackend3D` trait, so
marking whole methods or the trait unsafe would expand authority and could be
bypassed through trait dispatch. Instead, the 18 methods that actually reach
the canonical Vulkan ABI now contain leading lexical `unsafe(ffi)` blocks. All
64 foreign calls are covered while pure command-recording methods and the
public trait shape remain unchanged.

Boundary review added O(1) preflight guards: frame and texture dimensions must
be positive and at most 8192 per axis, each buffer allocation is capped at
256 MiB, buffer uploads reject invalid handles and negative offsets, and
texture uploads reject invalid handles. These checks occur before provider
calls and prevent unchecked geometry, allocation requests, and raw-handle use.

The command array, batching loops, handle-table layout, framebuffer cache, and
provider call count are unchanged. No allocation, copy, lookup, lock, hash,
signing operation, generic dispatch, or loop was added. The guards add one
constant-time branch only at resource creation/upload boundaries, not inside
the recorded-command drain loop.

The source census measured missing authority decreasing by exactly 64: 17,854
to 17,790 repository-wide and 9,685 to 9,621 in production. All 64 became
lexically scoped. The broader `rt_vulkan` family now has 270 explicit and 198
missing call sites. Exact-artifact verified-and-signed admission remains zero.

## Authoritative RT safety census checkpoint

After the VulkanBackend3D checkpoint, the fail-closed
`rt-safety-census.shs` evidence pipeline and its schema/total consistency
contract passed. Unlike textual estimates, this census joins declaration
source-signature hashes with the contract inventory and admits a row as
verified-and-signed only after all nine evidence inputs and the configured
Ed25519 trust policy verify.

Current exact declaration results are 11,627 rows / 3,139 distinct `rt_*`
symbols. All 11,627 remain classified unsafe. Of those, 2,441 declarations are
unsafe-tagged, 999 have documented contracts, 752 are unsafe-minimized, 10,875
remain unsafe-unminimized, and 8,939 are completely untouched. Evidence-
verified, signature-verified, and verified-and-signed rows are all zero.

Owned implementation definitions span four languages: Simple has 685
definitions / 644 symbols in 64 files; Rust has 2,132 / 2,110 in 173 files; C
has 2,396 / 1,894 in 89 files; and C++ has 219 / 219 in one file. These are
implementation-definition counts, not declarations or proof claims.

The call-authority census now also emits a per-file prioritization table from
the same captured call rows. It does not rescan source: aggregation remains
linear in the already-collected call-site count, and the table reports total,
distinct-symbol, lexical, function-level, and missing counts per owner. This
separates high-density owners from family-wide totals without adding a second
tree traversal.

## No-GC async CUDA facade checkpoint

The no-GC async CUDA API imports the canonical tagged CUDA declarations but
had 51 raw calls without local authority. Thirty-eight functions now use
leading lexical blocks: ordinary CUDA calls receive only `ffi`, while the
seven host-allocation, pointer-access, and bit-bridge methods also receive
`raw_ptr`. Class APIs and the canonical one-call wrapper functions retain
their existing signatures.

This checkpoint is compile-time metadata only. It changes no algorithm,
allocation, copy, provider call, loop, lookup, lock, hash, signing operation,
or dispatch. Review found multiple unchecked element-count products before
`count * 8` allocation/copy geometry; those functions remain unsafe and are
queued for a separate overflow-safe extent patch rather than being described
as verified.

The source census measured missing authority decreasing by exactly 51: 17,790
to 17,739 repository-wide and 9,621 to 9,570 in production. All 51 became
lexically scoped. The per-file table now reports this owner as 51 calls / 35
symbols / zero missing. The broader `rt_cuda` family has 138 explicit and 308
missing call sites. Exact-artifact verified-and-signed admission remains zero.

The queued extent patch now centralizes checked f64 byte and two-dimensional
product geometry. Counts above 33,554,432 f64 elements or 256 MiB are rejected
before multiplication, allocation, pointer offset, or device copy. Concatenate
uses subtraction-before-addition, and contiguous 2D copy hoists checked row
bytes outside its loop. Both constant-time helpers carry `@inline`; successful
operations retain the same allocation count, copy count, and loop complexity.
The unavailable production Simple binary prevents executable optimizer/runtime
evidence in this worktree, so the facade remains unsafe and unverified.
## Synchronous CLI SFFI facade checkpoint

`src/lib/nogc_sync_mut/sffi/cli.spl` contains 50 direct raw calls across
40 symbols.  Every call now has a minimal lexical `unsafe(ffi)` scope; the
public signatures and the existing boolean/status semantics are unchanged.
The facade remains O(1) direct delegation and gained no allocation, copy,
lookup, lock, hash, signature operation, or generic dispatch.  The focused
`nogc-sync-cli-sffi-authority.shs` audit passed and guards both the exact call
inventory and the absence of admission work on the call path.

The authoritative call census changed exactly as expected:

- missing authority: 17,739 -> 17,689
- lexical unsafe: 2,519 -> 2,569
- function unsafe: unchanged at 918

Static provider inspection found that `rt_compile_to_native` and
`rt_compile_to_native_with_opt` are not cross-lane ABI-safe: the Simple and
interpreter contracts return `(bool, text)`, but the standalone Rust runtime
exports `i64` functions that currently return a fabricated zero.  This
checkpoint does not coerce that integer into a tuple or claim the provider is
safe.  The ABI must be regenerated from one authoritative contract and the
zero stubs removed before these functions can be admitted outside their unsafe
boundary.

No production Simple optimizer/runtime measurement was possible because this
worktree has no production self-hosted binary.  The static shape evidence is
therefore useful but not performance verification.  Verified-and-signed SFFI
admission remains 0.

## Pure Simple SSH cipher boundary checkpoint

The general SSH cipher no longer declares or calls `serial_println` or
`rt_bytes_u8_at`; it remains a Pure Simple implementation.  Direct bounds-
checked indexing replaces the foreign byte accessor, and the packet hot path
no longer constructs an incrementally concatenated hexadecimal diagnostic or
prints secret-adjacent frame material.

AES-256-GCM now rejects non-32-byte keys, non-12-byte IVs, oversized or
inconsistent SSH frames, unexpected encryption output lengths, and unexpected
decryption plaintext lengths.  Nonces no longer silently zero-pad a short IV.
The focused `ssh-cipher-pure-boundary.shs` static ratchet passed.

The source change removes exactly two missing-authority raw call sites from
this caller, so the census baseline moves from 20,661 to 20,659 raw calls and
from 16,758 to 16,756 missing-authority calls; lexical and function unsafe
counts remain 2,984 and 919.  The valid path retains O(packet bytes) work and
existing packet buffers.  New checks are O(1), occur before allocation/copy
where possible, and add no hashing, signing, lookup, lock, dispatch, or copy.

This checkpoint is a source/static contract result, not production compiler
verification or signed artifact admission.  Repository-wide verified-and-
signed admission remains 0.

## Pure Simple SSH byte-utility checkpoint

`ssh_transport.spl`, `ssh_packet.spl`, and `ssh_kex_primitives.spl` now use
bounds-preserving Pure Simple indexing instead of `rt_bytes_u8_at`.
`ssh_identification.spl` now appends its already-masked byte directly instead
of calling `rt_push_byte`.  These modules consequently have no raw byte-
access/push declarations or calls; the focused
`ssh-pure-byte-boundary.shs` ratchet passed.

The authoritative census changed exactly by the four removed calls:

- raw call sites: 20,659 -> 20,655
- distinct called symbols: 3,261 -> 3,260
- caller files: 3,092 -> 3,088
- missing authority: 16,756 -> 16,752
- lexical unsafe: unchanged at 2,984
- function unsafe: unchanged at 919

Each replacement retains O(1) byte access and the existing O(n) surrounding
loops.  It removes foreign dispatch and adds no allocation, copy, hash,
signature operation, lookup, lock, or generic dispatch.  This is static source
evidence only; verified-and-signed artifact admission remains 0.

## SSH host-key loader contract checkpoint

The loader's local `rt_file_read_bytes` declaration now matches the
authoritative nullable `[u8]?` provider contract.  A missing or failed read is
lifted to `Result.Err` instead of being coalesced to an empty array and then
misreported as an empty file.  The remaining raw byte-to-text conversion is
centralized in one minimal `unsafe(ffi)` wrapper that rejects nil and rejects
an empty text fabricated from non-empty input.  The focused
`ssh-host-key-sffi-contract.shs` ratchet passed.

The authoritative census reflects two duplicate raw conversion calls removed
and the two retained wrapper calls bounded:

- raw call sites: 20,655 -> 20,653
- missing authority: 16,752 -> 16,748
- lexical unsafe: 2,984 -> 2,986
- function unsafe: unchanged at 919
- distinct called symbols/caller files: unchanged at 3,260 / 3,088

Valid reads and conversions preserve their existing O(file bytes) work and
allocation shape.  Error checks are O(1); no per-call hash, signature check,
lookup, lock, generic dispatch, or additional full-buffer copy was added.
Provider lanes still disagree on malformed byte-to-text behavior and no exact
artifact proof/signature receipt exists, so this module remains unsafe rather
than verified-and-signed; repository admission remains 0.

## SSH KEX call-authority and hot-path checkpoint

The SSH session KEX owner no longer dispatches its 113 constant packet-byte
appends through `rt_push_byte`; the retained local spelling is an inline Pure
Simple wrapper over `_append_byte`, so byte sequences and array-growth
semantics are unchanged.  Sixty-nine raw serial diagnostic calls were removed,
including transcript, public-key, signature, and exchange-hash hex formatting.
This removes foreign dispatch and avoids diagnostic text/hex allocations from
the handshake path.

The six remaining actual foreign calls in this owner are now inside minimal
lexical `unsafe(ffi)` scopes: X25519 public/shared operations, two SHA-256 KDF
calls, the exchange hash, and bounded retry sleep.  X25519 and SHA-256 results
must be exactly 32 bytes, the exchange hash must be exactly 32 bytes, derived
key lengths are checked before publication, and the KDF request is capped at
64 bytes.  A short/empty SHA-256 result now fails instead of leaving the KDF
expansion loop unable to make progress.

The focused static boundary ratchet passed.  The authoritative census changed:

- missing authority: 17,145 -> 17,070
- lexical unsafe: 2,954 -> 2,959
- function unsafe: unchanged at 919

The valid path adds fixed-width comparisons only and removes per-byte foreign
dispatch and diagnostic allocation work.  No hashing, signing, discovery,
lookup, lock, generic dispatch, or additional copy was added.  Provider ABI,
ownership, compiler/artifact identity, and proof receipts remain unresolved,
so SSH KEX and the wider SFFI surface are not globally safe, verified, or
signed; exact-artifact verified-and-signed admission remains 0.

## SSH session transport and sleep-ABI checkpoint

The parent SSH session owner replaced 41 fixed identification-byte calls to
the raw `rt_push_byte` provider with the same inline Pure Simple `_append_byte`
compatibility helper used by the KEX owner.  It also removed 81 raw serial
diagnostic calls, including ciphertext, packet, authentication, and version
formatting, and replaced the one runtime byte-slice call with the existing
bounded Pure Simple prefix copier.  This removes 123 raw call sites and avoids
diagnostic formatting/hex allocations on send, receive, and authentication
paths.

Provider inspection found that `rt_thread_sleep` is `void` in both
`runtime_thread.c` and the Rust executor.  The SSH declaration incorrectly
claimed an `i64` result; it now matches the provider and the KEX caller no
longer reads a fabricated return register.  Four bounded sleep calls and two
validated byte-to-text lifts use six minimal lexical `unsafe(ffi)` scopes.
Empty text lifts fail closed, send requires the provider to report the full
byte count, and receive sizes are checked against the facade's existing
16 MiB maximum before the `u64` to `i64` conversion.

The focused static boundary ratchet passed.  The authoritative census changed:

- raw call sites: 20,948 -> 20,825
- missing authority: 17,070 -> 16,941
- lexical unsafe: 2,959 -> 2,965
- function unsafe: unchanged at 919

The valid path removes foreign calls and diagnostic work.  Its added checks
are constant-time scalar comparisons; it adds no allocation, copy, hashing,
signature operation, discovery, lookup, lock, or generic dispatch.  The
network facade and providers still lack exact-artifact ABI/proof/signature
admission, so SSH and the broader SFFI surface remain not globally safe,
verified, or signed; exact-artifact verified-and-signed admission remains 0.

## Boot network facade contract and diagnostic checkpoint

The Pure Simple boot-network facade removed 27 serial diagnostic calls, its raw
runtime byte accessor, and one unreachable duplicate version-text provider
call; bounded Simple indexing now decodes already-sized SSH headers.  Normal
socket and identification reads now call the descriptor-aware provider with
the resolved owner instead of consulting the process-global receive stream.
This removes raw calls and formatting work without adding a lookup, allocation,
or copy.

The facade's `rt_thread_sleep` declaration now matches the C and Rust `void`
providers.  Write wrappers accept only the exact reported byte count (including
the fixed 22-byte SSH banner); reads reject results larger than their requested
extent; version text/bytes and plaintext SSH payloads have protocol bounds; and
foreign descriptors are range-checked before narrowing to `i32`.  A redundant
text conversion implementation and unused foreign declarations were removed.

The focused static contract ratchet passed.  The authoritative census changed:

- raw call sites: 20,825 -> 20,796
- missing authority: unchanged at 16,941
- lexical unsafe: 2,965 -> 2,936
- function unsafe: unchanged at 919

The valid path is cheaper: 29 raw calls disappeared and the new validation is
constant-time scalar/length comparison.  Exact provider ABI identity, artifact
signature verification, ownership evidence, and proof receipts remain absent,
so this facade and the broader SFFI surface are not globally safe, verified, or
signed; exact-artifact verified-and-signed admission remains 0.

## Thread-sleep ABI and authority checkpoint

The owned Simple source and tests contain 40 declarations and 55 calls of
`rt_thread_sleep`.  Both authoritative providers are void: C declares
`void rt_thread_sleep(int64_t)` and Rust exports
`extern "C" fn rt_thread_sleep(i64)` without a result.  The two SSH declarations
that claimed an `i64` return now match that ABI, and no caller reads a fabricated
return register.

Every declaration now carries explicit FFI metadata and every standalone call
is enclosed by the smallest lexical `unsafe(ffi)` scope.  This migration adds
compile-time authority only: it does not add a branch, wrapper dispatch,
allocation, copy, lookup, lock, hash, signature operation, or extra sleep.

The repository-wide ABI/authority ratchet passed.  The authoritative census
changed:

- raw call sites: unchanged at 20,796
- missing authority: 16,941 -> 16,905
- lexical unsafe: 2,936 -> 2,972
- function unsafe: unchanged at 919

The symbol is now consistently declared and explicitly unsafe, but provider
artifact identity and proof/signature receipts remain absent.  Therefore the
thread-sleep boundary and the broader SFFI surface are not globally verified
or signed; exact-artifact verified-and-signed admission remains 0.

## SSH helper Pure Simple boundary checkpoint

The SSH helper owner removed 28 per-byte foreign append calls, two raw slice
calls, one raw byte accessor, and two direct serial calls.  Its 37 parser and
validation diagnostic wrapper calls were also removed, avoiding text
interpolation and serial dispatch on malformed or ordinary handshake traffic.
Unused crypto, sleep, byte, and array extern declarations were deleted.

Byte access is now bounds-checked Simple indexing, ranges use the bounded
Simple slice operation, and the retained `rt_push_byte` spelling is an inline
Pure Simple `_append_byte` helper.  The only remaining foreign operation is a
byte-array-to-text lift in `_read_text_field_fast`; it has one minimal lexical
`unsafe(ffi)` scope and rejects non-empty input becoming empty text.  Length
parsing now uses subtraction-based overflow-safe bounds, and KEXINIT trailing
data is rejected instead of merely logged and accepted.

The focused static boundary ratchet passed.  The authoritative census changed:

- raw call sites: 20,796 -> 20,763
- missing authority: 16,905 -> 16,871
- lexical unsafe: 2,972 -> 2,973
- function unsafe: unchanged at 919

The valid byte-building path removes foreign dispatch and adds only constant-
time bounds checks already required before indexing.  No lookup, lock, hash,
signature operation, generic dispatch, or extra copy was introduced.  The
remaining text provider lacks exact-artifact proof/signature admission, so the
SSH helper family and wider SFFI surface remain not globally verified or
signed; exact-artifact verified-and-signed admission remains 0.

## SSH interactive channel and SCP boundary checkpoint

The SSH channel owner removed 24 raw serial diagnostics, four per-byte append
calls, five whole-array concatenations, two raw slices, and three duplicate
byte-to-text calls.  Raw byte scanning now uses the bounds-checked Pure Simple
SSH helper, while basename and command paths use already-validated Simple
slices.

SCP control records now collect decimal digits in reverse once and append them
directly into the output, followed by one pass over the filename.  This removes
the former temporary one-byte array and prepend-concatenation for every digit,
plus four subsequent whole-array concatenations.  The algorithm remains linear
but performs fewer allocations and copies.

One generated text-lift wrapper rejects non-empty input becoming empty text.
The four x86_64 FAT/MMIO declarations now carry explicit `ffi`/`raw_ptr`
authority and their calls use minimal lexical scopes.  File sizes remain capped
at 4 MiB; the buffer extent cannot overflow its address; stream reads must
report the exact size before MMIO access.  The existing bounded sleep retains
one minimal lexical scope.

The focused static boundary ratchet passed.  The authoritative census changed:

- raw call sites: 20,763 -> 20,725
- distinct called symbols: 3,263 -> 3,261
- missing authority: 16,871 -> 16,828
- lexical unsafe: 2,973 -> 2,978
- function unsafe: unchanged at 919

No hashing, signing, lookup, lock, generic dispatch, or additional data copy
was introduced.  FAT/MMIO ownership and exact provider artifact/proof/signature
evidence remain unresolved, so the channel family and wider SFFI surface are
not globally verified or signed; exact-artifact verified-and-signed admission
remains 0.

## SSH authentication Pure Simple checkpoint

The split SSH service-request/authentication owner no longer declares or calls
the raw serial provider.  Thirteen packet/authentication diagnostic calls were
removed, including full pre-auth packet hex formatting.  The module now has no
foreign declaration or call.

Authentication semantics are unchanged: booleans remain booleans, malformed
text fields fail through the hardened helper `Result`, password fields are not
copied to immutable text, request attempts remain bounded, and equal-length
credential comparisons still visit every byte with an accumulated XOR.

The focused Pure Simple boundary ratchet passed.  The authoritative census
changed:

- raw call sites: 20,725 -> 20,712
- caller files: 3,094 -> 3,093
- missing authority: 16,828 -> 16,815
- lexical unsafe: unchanged at 2,978
- function unsafe: unchanged at 919

This removes formatting, allocation, and foreign dispatch from pre-auth paths;
it adds no work to successful or rejected authentication.  Providers used by
lower transport/crypto owners remain without exact-artifact proof/signature
admission, so the wider SSH/SFFI surface is not globally verified or signed;
exact-artifact verified-and-signed admission remains 0.

## SSH daemon tokenization and provider-honesty checkpoint

The daemon owner removed 36 serial diagnostics, its raw byte accessor/append
calls, and one duplicate byte-to-text call.  Deferred-command tokenization now
converts the command to bytes once, indexes and appends in Pure Simple, and uses
one typed text-lift helper that rejects empty or failed token conversion.

The intentional RV64 boot-network bypass remains, because replacing it would
change the selected transport architecture.  Its bind and one-shot accept
providers now carry explicit FFI metadata, run in minimal lexical scopes, and
reject negative or non-`i32` descriptors after normalization.  No lookup,
allocation, or dispatch was added to accept polling.

Review also removed startup prose and diagnostics claiming an Ed25519 self-test
had passed.  No such self-test was invoked in this owner; configured credential
presence, exact 32-byte key lengths, and host-key policy are the actual current
admission checks.  The focused ratchet prevents restoring the unsupported
verification claim.

The focused static boundary ratchet passed.  The authoritative census changed:

- raw call sites: 20,712 -> 20,673
- missing authority: 16,815 -> 16,773
- lexical unsafe: 2,978 -> 2,981
- function unsafe: unchanged at 919

The hot command/accept paths are cheaper because raw diagnostics and per-byte
foreign work disappeared.  The boot TCP and text providers still lack exact-
artifact ABI/proof/signature evidence, and Ed25519 is not newly verified by
this checkpoint.  SSH and the wider SFFI surface remain not globally verified
or signed; exact-artifact verified-and-signed admission remains 0.

## SSH live cipher contract checkpoint

The SSH live cipher removed eleven secret-bearing serial diagnostics and its
raw byte accessor.  Key, IV, nonce, AAD, plaintext, ciphertext, tag, and packet
bytes are no longer hex-formatted on encrypt/decrypt paths, and byte reads use
an inline bounds-checked Pure Simple helper.

The three AES-256 providers now carry explicit FFI metadata and are called from
three minimal lexical scopes.  AES-256 requires a 32-byte key; AES-128 requires
16 bytes; both require a 12-byte IV/nonce and an exact bounded SSH GCM frame.
Encrypt output must be plaintext length plus the 16-byte tag.  The Rust decrypt
provider's status-prefixed contract is now enforced exactly: `0x00` is tag
mismatch, only `0x01` is success, and success length must equal ciphertext
length plus the status byte.  The direct packet provider must return a nonempty
payload no larger than the authenticated packet body.

Malformed short IVs previously became zero-padded nonces.  They now fail before
encryption/decryption rather than manufacturing nonce bytes.  The valid nonce
path also removes twelve repeated IV-length branches after its single exact-
length check.

The focused Simple/provider ratchet passed.  The authoritative census changed:

- raw call sites: 20,673 -> 20,661
- missing authority: 16,773 -> 16,758
- lexical unsafe: 2,981 -> 2,984
- function unsafe: unchanged at 919

The new validation is constant-time scalar/length comparison.  No allocation,
copy, lookup, lock, hashing, signature operation, or generic dispatch was added.
Exact provider artifact/proof/signature evidence remains absent, so the cipher
and wider SFFI surface are not globally verified or signed; exact-artifact
verified-and-signed admission remains 0.

## Synchronous SIMD SFFI facade checkpoint

`src/lib/nogc_sync_mut/simd.spl` has 48 direct calls to 47 `rt_simd_*`
symbols.  All 48 calls now carry minimal lexical `unsafe(ffi)` authority.  The
focused `nogc-sync-simd-sffi-authority.shs` audit passed and ratchets the call
and scope counts.  It also rejects per-call signature verification, symbol
lookup, locking, or generic FFI dispatch in these instruction-level hot paths.

The raw profile result previously mapped every unknown discriminant to
`SimdTier.scalar`, manufacturing a valid capability state from a provider
contract violation.  Unknown values now fail closed; the nine valid match arms
are unchanged.  Normal calls retain one direct foreign call and the same data
movement, allocation count, and asymptotic complexity.  No C/Rust replacement
for the Pure-Simple vector/ML-KEM algorithms was introduced.

The authoritative call census changed exactly as expected:

- missing authority: 17,689 -> 17,641
- lexical unsafe: 2,569 -> 2,617
- function unsafe: unchanged at 918

Native Rust providers lower several vector structures through scalar lanes and
out pointers, whereas the interpreter exposes typed `Value` structures.  This
can be a compiler-owned lowering convention, but the current source census is
not an ABI fingerprint or cross-lane proof.  Consequently these wrappers are
unsafe-bounded, not verified or signed.  No production optimizer or runtime
benchmark was available in this worktree; performance evidence is limited to
the unchanged direct-call source shape.  Verified-and-signed admission remains
0.
## SimpleOS socket facade SFFI checkpoint

`src/os/kernel/net/rt_net_socket_facade.spl` is a Pure-Simple socket owner over
19 boot/runtime declarations.  All declarations now carry explicit
`@unsafe(... ffi)` metadata and all 50 calls use minimal lexical `unsafe(ffi)`
scopes.  No C or Rust replacement was introduced.  The focused
`os-net-socket-sffi-authority.shs` audit passed and ratchets declaration and
call inventories while rejecting per-call admission, lookup, locks, and generic
dispatch.

The same checkpoint closes bounded-input defects before entering the provider:

- reject ports outside 0..65535 before `u16` conversion while preserving port
  zero for ephemeral binding;
- cap exact SSH reads at 35,016 bytes and reject provider chunks larger than
  the requested remainder;
- cap the generic socket read request at 16 MiB;
- reject plaintext SSH packet lengths above 35,000 bytes before allocation;
- validate cached-payload slice signs and subtraction-first extents before
  forming the end index.

These are O(1) guards.  Normal paths keep the same direct calls, loop
complexity, copies, and persistent socket layout; worst-case foreign-controlled
allocation is reduced.  The authoritative call census changed exactly as
expected:

- missing authority: 17,641 -> 17,591
- lexical unsafe: 2,617 -> 2,667
- function unsafe: unchanged at 918

The provider still uses legacy empty-array/empty-text error sentinels in APIs
that cannot distinguish transport failure from valid empty data.  Correcting
that requires an ABI-versioned `Result`/status contract across all consumers;
this checkpoint does not fabricate a local distinction.  No production
self-hosted runtime was available for executable optimizer or RSS evidence, so
the lane is unsafe-bounded, not verified.  Verified-and-signed admission
remains 0.
## Standard-library file I/O SFFI checkpoint

The synchronous file facade now has explicit authority on all 36 declarations
and minimal lexical scopes on all 47 calls.  Four previously unscoped calls in
the related mmap facade were also bounded; its seven declarations and seven
calls are now all explicit.  The focused `stdlib-file-io-sffi-contract.shs`
audit passed.

Provider review found and corrected contract defects rather than working around
them:

- `rt_file_get_size` is registered as `i64`; native now returns signed `i64`
  and uses `-1` for invalid descriptors, metadata failure, and overflow rather
  than fabricating zero.  Both Simple declarations now match.  The legacy
  `Option<i32>` facade narrows only representable values.
- `file_size()` now calls the actual `rt_file_size` provider instead of
  misinterpreting the modification-time `rt_file_stat` result as bytes.
- text, line-list, byte-array, and directory-list nil failures remain distinct
  from valid empty values in safe `Result` wrappers.  The explicitly `_unsafe`
  compatibility wrappers retain their documented empty sentinels.
- `is_dir()` now calls the semantic boolean provider instead of allocating a
  directory listing and returning the always-true expression `len >= 0`.
- `rt_dir_create` and `rt_dir_remove` now pass the required recursive boolean
  argument explicitly, eliminating an ABI register mismatch.

The authoritative census changed exactly as expected:

- missing authority: 17,591 -> 17,540
- lexical unsafe: 2,667 -> 2,718
- function unsafe: unchanged at 918

The focused Rust descriptor test passed (`1 passed`, 1,226 filtered) and now
distinguishes an empty file size of zero from invalid descriptor failure `-1`.
Normal file operations retain direct calls and their existing I/O complexity;
the semantic directory query removes a directory scan and result allocation.
No per-operation hashing, signature work, discovery, lock, or generic dispatch
was added.  Production Simple optimizer/performance evidence remains
unavailable in this worktree.  Glob/find/walk and some legacy unsafe helpers
still have empty-result ambiguity, so this lane is not globally verified or
signed; verified-and-signed admission remains 0.
## Debug/ptrace/DWARF SFFI checkpoint

`src/lib/nogc_sync_mut/sffi/debug.spl` has 43 raw declarations and calls.
Every call now has a minimal lexical `unsafe(ffi)` scope; the pre-existing raw
DWARF handle wrapper remains function-level unsafe.  The focused
`debug-sffi-authority.shs` audit passed.  It records 14 observed Rust debugger
providers and 29 declarations with no repository-owned provider.  Missing
debugger, ptrace, and DWARF providers remain raw/unsafe and link-fail-closed;
no nil/zero stub was added.

Breakpoint ABI review corrected three concrete defects:

- add now uses the provider's three-argument signature and signed ID/status
  result rather than passing an invented fourth ID argument;
- remove now declares its signed status result, and clear uses the actual
  `rt_debug_remove_all_breakpoints` symbol;
- the Rust add/remove/query providers reject null, negative/unrepresentable
  extents, invalid lines, and invalid UTF-8 instead of constructing unchecked
  slices and calling `from_utf8_unchecked`.

A semantic `rt_debug_has_breakpoint` provider was added without mutating hit
counters.  Boolean wrappers use an inline total 0/1 contract and fail closed on
invalid discriminants rather than treating every nonzero integer—including an
error sentinel—as true.  Nonexistent raw exports were removed from the facade.

The authoritative census changed as expected for the 42 previously missing
calls (the DWARF load call was already function-unsafe):

- missing authority: 17,540 -> 17,498
- lexical unsafe: 2,718 -> 2,760
- function unsafe: unchanged at 918
- distinct called symbols: 3,267 -> 3,266 after consolidating the clear symbol

The focused Rust breakpoint contract test passed (`1 passed`, 1,227 filtered).
Normal debugger state calls remain direct.  The new validation is limited to
breakpoint mutation/query boundaries and adds no hashing, signing, discovery,
generic dispatch, or long-lived allocation.  Ptrace/DWARF and 15 debugger
operations are still unavailable, so the module is not verified or signed;
verified-and-signed admission remains 0.

## Artifact-manifest signed-admission boundary checkpoint

The generic artifact manifest has one freestanding raw call: byte access while
hex-encoding its Pure Simple SHA-256 digest.  Its declaration and call now have
minimal `unsafe(ffi)` authority.  The wrapper requires an exact 32-byte digest
and a returned byte in 0..255 before encoding; invalid runtime behavior traps
instead of manufacturing an empty or malformed identity.

The loader-owned Ed25519 verifier now also rejects non-canonical image and
trust-root identities before signing-body construction.  Both must be exactly
64 lowercase hexadecimal characters.  Existing admission still requires a
three-field Ed25519 envelope, a 64-byte decoded signature, a private trusted
signer capsule, an exact trust-root hash, canonical signing bytes, and a Pure
Simple Ed25519 verification result.  The package-private receipt remains the
authority carrier; caller-supplied booleans cannot construct an executable
handle, and the verifier call precedes handle construction.

The focused `artifact-manifest-admission-contract.shs` ratchet passed.  The
authoritative call census changed by the one newly bounded accessor:

- missing authority: 17,259 -> 17,258
- lexical unsafe: 2,953 -> 2,954
- function unsafe: unchanged at 919

Hashing, trust-root lookup, locking, and signature verification remain
load-time admission work, not per-executable-call work.  The new identity
checks are two bounded 64-character scans before much more expensive Ed25519
verification and allocate no arrays.  No production self-hosted executable was
available for the signature fixtures.  This proves a local fail-closed source
shape, not that any exact provider artifact has a verified receipt; repository
verified-and-signed admission remains 0.

## SimpleOS Ed25519 Pure-Simple boundary checkpoint

`src/os/crypto/ed25519.spl` previously claimed to be Pure Simple while still
containing 45 raw calls: 41 unconditional `serial_println` diagnostics, three
runtime crypto-helper calls with no non-vendored C or Rust provider, and a
runtime byte-index helper.  The focused `ed25519-pure-boundary.shs` audit now
requires zero raw extern declarations and calls in this module.

The public Ed25519 implementation remains Pure Simple.  Native Simple array
indexing replaces the raw byte-index helper.  The phantom SHA-512/scalar helper
backend was removed; the canonical checked signature facade is compared
directly with the existing Pure Simple signature.  Exact 32-byte key and
64-byte signature contracts are enforced, provider disagreement returns an
error, and the `runtime_only` API no longer silently succeeds through a Pure
Simple fallback after provider failure.

All production tracing, signature hex formatting, and the 32-byte scalar probe
copy were removed.  Dual-run metadata is now constructed only after the normal
mode returns, eliminating its common-path empty-array allocation.  This removes
I/O and allocation from signing rather than adding checks to its inner scalar
or hash loops.

The authoritative census changed by removing all 45 former call sites:

- missing authority: 17,304 -> 17,259
- lexical unsafe: unchanged at 2,953
- function unsafe: unchanged at 919

This establishes the local Pure-Simple boundary and fail-closed result shape;
the production self-hosted binary was unavailable for an RFC 8032 executable
vector or optimizer run.  The checkpoint therefore does not prove the
Ed25519 arithmetic, compiler, loader, or exact artifact.  Repository
verified-and-signed admission remains 0.

## TLS 1.3 handshake SFFI checkpoint

All 49 raw calls in the TLS 1.3 handshake driver now have minimal lexical
`unsafe(ffi)` scopes.  The focused `tls13-handshake-sffi-contract.shs` ratchet
passed and uses an identifier-boundary matcher so ordinary names containing an
`rt_` substring are not counted as foreign calls.

Foreign-result review closed several fail-open and bounds defects:

- ServerHello and post-HRR payload lengths must be at least a handshake header,
  no larger than 18,432 bytes, and fit within the returned record before any
  subtraction or copy;
- ClientHello records must contain the five-byte TLS record header;
- the implemented handshake accepts only its documented
  `TLS_AES_128_GCM_SHA256` suite;
- X25519 keys, SHA-256 hashes, derived secrets, traffic keys/IVs, and Finished
  keys/data must have their exact contract lengths;
- foreign handshake messages must contain at least their four-byte header
  before body slicing;
- empty expected and received Finished values can no longer compare equal and
  authenticate a server.

The authoritative census changed exactly by the 49 newly bounded calls:

- missing authority: 17,353 -> 17,304
- lexical unsafe: 2,904 -> 2,953
- function unsafe: unchanged at 919

The valid path adds scalar length/discriminant comparisons only; it adds no
allocation, copy, lookup, lock, hashing, signature verification, discovery, or
generic dispatch.  A redundant post-validation Finished comparison was
removed.  The fixed bootstrap key path, remaining TLS call sites, provider
proof obligations, and exact-artifact signatures remain unresolved, so TLS is
not globally verified or signed; verified-and-signed admission remains 0.

## TLS 1.3 context-I/O call-authority checkpoint

The TLS 1.3 context owner retains 48 operation-specific raw declarations and
now places all 17 actual raw calls in minimal lexical `unsafe(ffi)` scopes.
The focused `tls13-context-sffi-contract.shs` ratchet passed and excludes
function-name substrings from its raw-call scan.

Review found an extent defect before the IPC receive boundary.  The direct
receive helper previously narrowed arbitrary `u64` lengths to `u32` and then
computed `max_len + 16` for the foreign receive allocation.  It now rejects
zero and values above the existing RFC 8446 record payload bound of 18,432
bytes before either operation.  Valid TLS records keep the same calls, copies,
loops, and allocation sizes.

The authoritative census changed exactly by the 17 newly bounded calls:

- missing authority: 17,370 -> 17,353
- lexical unsafe: 2,887 -> 2,904
- function unsafe: unchanged at 919

The new valid-path check is constant-time and prevents oversized work.  No
hashing, signing, discovery, lock, allocation, copy, or generic dispatch was
added.  The wider handshake driver still contains unbounded raw calls and the
TLS providers lack exact-artifact signed proof receipts, so the TLS family is
not globally verified or signed; verified-and-signed admission remains 0.

## HTTP/WebSocket call-authority checkpoint

The three legacy HTTP/WebSocket facades each retain 26 explicitly tagged raw
declarations and now place all 29 wrapper calls in minimal lexical
`unsafe(ffi)` scopes.  The focused `http-sffi-call-authority.shs` ratchet
passed: 78 declarations and 87 calls are covered without making the entire
safe-looking wrapper functions unsafe.

Provider inspection confirms that coverage remains partial.  Native C owns
GET, generic request, download, and client lifecycle/request operations; the
Rust interpreter owns GET and generic request.  The other declared operations
remain unsafe and link-fail-closed.  No zero, false, empty-text, or nil provider
stub was added.  The active native response reader's existing 64 MiB bound is
retained.

The authoritative census changed exactly by the 87 newly bounded calls:

- missing authority: 17,457 -> 17,370
- lexical unsafe: 2,800 -> 2,887
- function unsafe: unchanged at 919

Lexical capability scopes are compile-time metadata and add no network work,
allocation, copy, lookup, lock, branch, hashing, signing, or generic dispatch.
No production self-hosted optimizer or benchmark was available.  Missing
providers, ambiguous WebSocket empty-text receive semantics, TLS policy, and
artifact evidence remain unresolved, so the family is not globally verified
or signed; verified-and-signed admission remains 0.

## GLFW SFFI contract and dispatch checkpoint

The hosted GLFW facade has 40 raw declarations and 41 raw calls.  All
declarations now carry explicit FFI authority and all calls are covered by 24
minimal lexical scopes; the raw ARGB word-pointer path additionally requires
`raw_ptr`.  The focused `glfw-sffi-contract.shs` audit passed.

Provider and wrapper review corrected contract defects instead of converting
them to convenient values:

- invalid window handles now make `rt_glfw_should_close` return `-1`; the
  Simple wrapper accepts only the semantic 0/1 boolean domain;
- unavailable or invalid clipboard access returns null and lifts to `text?`,
  preserving a valid empty clipboard string as distinct from absence;
- window and frame dimensions are bounded to 8192 and frame input to 256 MiB
  before allocation or byte access;
- the Rust interpreter bridge caches each resolved typed-family symbol in a
  fixed atomic slot, eliminating its prior `dlsym` on every event/frame call.

The authoritative census changed exactly by the 41 newly bounded calls:

- missing authority: 17,498 -> 17,457
- lexical unsafe: 2,760 -> 2,800
- function unsafe: 918 -> 919 (the raw-pointer method is now explicitly unsafe)

GNU C11 syntax validation and the focused Rust GLFW bridge tests passed.  The
cached path adds no hashing, signature operation, mutex, allocation, or symbol
lookup; its remaining signature-table scan is fixed at 41 entries and predates
this checkpoint.  No production self-hosted optimizer or benchmark was
available.  GLFW lifetime, callback, and artifact-evidence obligations remain
unsafe, so this module is not globally verified or signed; verified-and-signed
admission remains 0.
