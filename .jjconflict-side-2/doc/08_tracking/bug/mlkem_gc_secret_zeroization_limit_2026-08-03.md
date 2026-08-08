# ML-KEM GC secret-zeroization limitation

Status: CLOSED — accepted limitation (NFR-005 re-scoped per AC-10, decided
2026-08-05, T-10 of `doc/03_plan/agent_tasks/x25519mlkem768_remaining_tasks.md`)

## Scope

ML-KEM key generation, encapsulation, and decapsulation use GC-managed `list`
values. Function-owned lists are mutable and can be overwritten, but the
current runtime does not guarantee that collection, movement, hash/sponge
internals, tuple transport, or compiler temporaries leave no stale copies.
Consequently, pure-Simple list cleanup is best effort rather than a secure-zero
primitive.

## Implemented mitigation

`src/os/crypto/ml_kem.spl` now overwrites function-owned secret-key slices,
encapsulation/decapsulation concatenation buffers, FO messages and coins,
candidate and implicit secrets, and error-path temporaries immediately after
their result has been copied or constant-time selected. It deliberately does
not mutate caller-owned seeds, keys, ciphertexts, or messages. Native SIMD and
CUDA/Metal staging buffers have separate bounded wipe/clear lifecycles. The
pinned A/B/C workload and SIMD measurement harness also overwrite their owned
fixture seeds, returned decapsulation keys, typed X25519 private-key copies,
shared secrets, and digest temporaries through deferred cleanup on normal and
error exits. These additions narrow lifetime but do not strengthen the
physical-erasure claim.

The absolute spec verifies that complete keygen/encapsulation/decapsulation
still produces matching secrets and leaves every caller-owned input unchanged.
This proves ownership behavior, not physical-memory erasure.

## Remaining exposure

- GC or compiler-created copies may outlive the overwritten list;
- SHA3/SHAKE state and K-PKE polynomial temporaries lack a canonical secure
  owner type and optimizer-resistant destruction contract;
- returned private keys and shared secrets remain caller-owned until the TLS
  handshake owner releases them;
- no heap-forensics or allocator-reuse evidence exists yet.

## Closure criteria (for a future Path A — not undertaken here)

1. Add a canonical non-moving/explicitly destroyed secret-byte owner or a
   runtime-backed secure-zero primitive with a documented optimization ABI.
2. Thread it through entropy, ML-KEM, X25519, and TLS ephemeral ownership without
   exposing secret values through evidence or formatting.
3. Verify normal and error-path destruction, allocator reuse, and no secret
   diagnostic output under an admitted source-matched runtime.
4. Retain caller-input ownership tests and native GPU/SIMD cleanup evidence.

## T-10 decision (2026-08-05)

**Decision: Path B — re-scope NFR-005, not Path A (canonical primitive).**

Investigated whether an existing non-GC primitive makes Path A cheap. Found
`src/lib/nogc_sync_mut/mimalloc_secure.spl` (`mi_malloc_secure` /
`mi_free_secure`, an `@no_gc` module), but it is a kernel/baremetal-facing raw
allocator (`mi_malloc_raw` returns a `VirtAddr`-typed `usize`), not a userland
type usable from `src/os/crypto/ml_kem.spl` without a new FFI/ownership layer.
Adopting it would require: (a) a new secret-byte owner type bridging raw
kernel memory into hosted crypto code, (b) rewriting the K-PKE/NTT/Keccak hot
path off GC-managed `list`/`[u8]` onto that type — which does not by itself
stop the compiler from re-copying values read out of raw memory into local
GC-managed temporaries, so it does not close the exposure without further
compiler cooperation, (c) new allocator-reuse/heap-forensics verification that
does not exist anywhere in the codebase today. This matches the closure
criteria list above almost exactly — it is a new subsystem, not a bounded fix.
Given this campaign is at its tail (T-10 of 11), and AC-10 explicitly permits
re-scoping with limitations "documented and tested where observable," Path B
is the correct call.

**Observability test (already existed, verified passing):**
`test/01_unit/os/crypto/x25519mlkem768_hybrid_support_spec.spl`, example
"wipes every owned list and byte-array element including empty inputs" (lines
73-85), exercises `x25519_mlkem768_wipe_owned` /
`x25519_mlkem768_wipe_owned_bytes` and asserts the owned slice reads back all
zero afterward. This is the observable half of NFR-005: it proves the
best-effort mitigation actually zeroes the memory it can reach. Run
2026-08-05: `SPEC FILE VERDICT: test/01_unit/os/crypto/x25519mlkem768_hybrid_support_spec.spl
declared>=11 executed=11 passed=11 failed=0 dropped=0`.

The negative half — a secret surviving in an unreachable-but-not-yet-collected
GC/compiler copy — is judged **not observable** with a userland Simple spec:
there is no heap-forensics or allocator-introspection API in this codebase
(confirmed by grep; the only related primitive is the kernel-facing
`mimalloc_secure.spl` above, which is not reachable from hosted crypto code).
Building one would itself be Path-A-scale work. Per AC-10's "tested where
observable" clause, this half is documented, not test-asserted with a
fabricated or unverifiable check.

**Docs updated to state accepted scope:** `doc/02_requirements/nfr/x25519mlkem768_acceleration.md`
(NFR-005) and `doc/04_architecture/x25519mlkem768_acceleration.md` (Security
boundaries).
