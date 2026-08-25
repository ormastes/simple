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
