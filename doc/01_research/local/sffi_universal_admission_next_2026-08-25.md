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
