<!-- codex-research -->
# Domain research: X25519MLKEM768 acceleration

Date: 2026-08-02

## Standards baseline

[NIST FIPS 203](https://csrc.nist.gov/pubs/fips/203/final) is the normative ML-KEM definition. It defines ML-KEM-512/768/1024 and relates security to Module-LWE. NIST currently flags a pending erratum, so implementations and fixtures need an explicit FIPS/profile revision instead of an unversioned `mlkem768` label.

Official deterministic validation should use the [NIST ACVP ML-KEM schema](https://pages.nist.gov/ACVP/draft-celi-acvp-ml-kem.html) and NIST ACVP vector sets. ML-KEM-768 sizes are 1184-byte encapsulation key, 2400-byte expanded decapsulation key, 1088-byte ciphertext, and 32-byte shared secret.

The current TLS definition is [draft-ietf-tls-ecdhe-mlkem-05](https://datatracker.ietf.org/doc/html/draft-ietf-tls-ecdhe-mlkem-05), not yet an RFC. It assigns the Recommended TLS NamedGroup `4588` (`0x11ec`) and specifies:

- client share: `ML-KEM encapsulation key || X25519 share` = 1216 bytes;
- server share: `ML-KEM ciphertext || X25519 share` = 1120 bytes;
- hybrid secret: `ML-KEM shared secret || X25519 shared secret` = 64 bytes;
- invalid encapsulation key or wrong ciphertext/X25519 value: fail closed with the specified TLS alert;
- X25519 all-zero shared-secret rejection;
- obsolete draft Kyber code points must not be accepted as the standardized group.

## Free/open comparison implementations

### Primary oracle: mlkem-native

[mlkem-native](https://github.com/pq-code-package/mlkem-native) is actively maintained and offers portable C, x86-64 AVX2, AArch64, and RVV work, with substantial CBMC/HOL-Light assurance. Its permissive Apache-2.0/ISC/MIT licensing, deterministic interfaces, and [benchmark suite](https://pq-code-package.github.io/mlkem-native/dev/bench/) make it the strongest comparison target. It should be used as an external oracle, not copied blindly into Simple.

### Secondary oracles

- [Cloudflare CIRCL](https://github.com/cloudflare/circl) is BSD-3-Clause and supplies FIPS 203 ML-KEM plus X25519; it is useful for independent differential checks but carries an experimental-use disclaimer.
- [Go crypto/mlkem](https://pkg.go.dev/crypto/mlkem) and [crypto/tls](https://pkg.go.dev/crypto/tls) provide a BSD-licensed standardized API/TLS implementation in current Go releases.
- [OpenSSL 3.5](https://docs.openssl.org/3.5/man3/SSL_CONF_cmd/) provides standardized ML-KEM and hybrid TLS behavior under Apache-2.0 and is useful for live interoperability.
- [liboqs](https://github.com/open-quantum-safe/liboqs) integrates mlkem-native and multiple optimized variants, but explicitly positions itself as a prototyping library.
- PQClean is permissively licensed but is being archived in favor of PQ Code Package and should not be the primary long-lived oracle.

Go and CIRCL are independent output comparators, not authorities for selecting
the repository workload. OpenSSL covers useful ML-KEM/TLS interoperability but
does not expose the complete deterministic five-input hybrid fixture. The
repository must therefore own one data-only fixture and a semantic digest over
the exact ordered `client_private`, `d`, `z`, `server_private`, and `m` bytes.
Public-key/output comparison alone is insufficient: X25519 clamps private-key
bits, and a valid ML-KEM decapsulation need not expose `z`.

## SIMD design lessons

Successful implementations keep one scalar specification and specialize narrow kernels: NTT/inverse NTT, base multiplication, rejection sampling, polynomial encode/decode, and Keccak. Runtime dispatch must be feature-accurate and outputs byte-identical.

- x86: AVX2 is the practical baseline on the current host.
- ARM: AArch64 NEON is established upstream; SVE/SVE2 can remain a later extension.
- RISC-V: RVV must be vector-length agnostic and tested across multiple VLENs; compiler autovectorization alone is not execution proof.

## GPU design lessons

[NVIDIA cuPQC](https://developer.nvidia.com/cupqc) demonstrates that ML-KEM can achieve very high batched throughput, but the SDK is not a reusable free/open implementation even though its samples are Apache-2.0. It is a performance reference only.

GPU acceleration should be batch-only by default. Measurements must amortize upload, launch, synchronization, and readback and must not infer a single-handshake win from bulk throughput. Persistent executors and compiled-artifact caches are essential.

No authoritative maintained ML-KEM Vulkan or Metal implementation was found. Those backends should be treated as experimental until device-origin output, absolute oracle parity, constant-time/divergence review, and retained performance evidence succeed. TLS long-term secrets must not be sent through shared or untrusted GPU contexts.

## Recommended test model

1. NIST ACVP key generation, encapsulation, decapsulation, key-check, invalid-key/ciphertext, and implicit-rejection cases; RFC 7748 X25519 vectors.
2. Identical deterministic `d`, `z`, `m`, X25519 scalar, public key, ciphertext, and expected hybrid bytes through Simple scalar and pinned mlkem-native plus OpenSSL/Go/CIRCL.
3. Backend equivalence/property tests across AVX2, NEON, RVV VLENs, CUDA, Vulkan, and Metal with independent execution receipts and device readback.

Performance evidence should record cold and warm setup, keygen/encap/decap/combine, batch sizes, p50/p95/p99, throughput, RSS/device memory, transfer/sync/readback, backend identity, fallback state, source/artifact hashes, and fixture hash.

## 2026-08-03 standards and deployment refresh

The IETF document remains `draft-ietf-tls-ecdhe-mlkem-05`, but its status has
advanced: after RFC Editor processing began, the working group obtained
consensus to change X25519MLKEM768 from `Recommended: N` to `Recommended: Y`.
The second IETF Last Call closed on 2026-06-09. The current draft still fixes
NamedGroup `4588`, the ML-KEM-before-X25519 share ordering, and the
ML-KEM-before-X25519 64-byte secret ordering. This strengthens the product
default rationale but does not justify calling the draft an RFC before final
publication.

NIST's FIPS 203 publication page now carries a 2025-11-17 planning note that a
known issue will be corrected in a future update or revision. The implementation
must therefore keep the exact FIPS/profile revision in config, artifacts, cache
keys, and receipts; a bare `ML-KEM-768` identity is still insufficient.

Deployment comparison has also matured. Go documents X25519MLKEM768 (`4588`) as
a default since Go 1.24. OpenSSL 3.5 places X25519MLKEM768 first in its default
group list, while OpenSSL 3.6 warns that the larger ClientHello can expose broken
middleboxes or firewalls when it crosses a TCP-segment boundary. System tests
should therefore retain a fragmented/large-ClientHello interoperability row;
silently disabling the hybrid group is not the correct failure policy.

## 2026-08-04 key storage and combiner scope note

NIST's [PQC FIPS FAQ](https://csrc.nist.gov/Projects/post-quantum-cryptography/faqs),
revised 2026-06-16, explicitly permits a module to retain the 64-byte `(d, z)`
seed pair as the private-key representation and regenerate the expanded ML-KEM
encapsulation/decapsulation keys with the internal key-generation algorithm.
This can materially reduce key-at-rest size and secret exposure, but it is an
optional storage profile: the current 2400-byte expanded-key API and fixtures
must not silently reinterpret their inputs. A seed-backed profile needs its own
versioned key representation, deterministic expanded-key parity tests, import
and export policy, wiping evidence, and regenerated-key self-test.

The TLS working-group draft's security considerations also state that the
hybrid construction relies on the TLS 1.3 transcript and must not be assumed
secure when copied into another protocol. The repo's raw composition helpers
are therefore byte-level primitives, not a general-purpose authenticated key
exchange. Promotion evidence for the web server/browser path must cover the
actual TLS transcript, HelloRetryRequest, downgrade resistance, and alert
behavior rather than only comparing the 64-byte concatenated secret.
## GCC cross-target branch-denominator research (2026-08-04)

GCC 13.3 `gcov -j -b -c` is suitable for the runtime C denominator because
`-j` emits gzip-compressed JSON without requiring source during generation,
`-b` includes branch records, and `-c` reports exact taken counts rather than
percentages. The JSON binds GCC version, compilation working directory, data
file, source file, functions, lines, and branch `count`/`fallthrough`/`throw`
metadata. Source: <https://gcc.gnu.org/onlinedocs/gcc-13.3.0/gcc/Invoking-Gcov.html>.

The same GCC documentation warns that multiple basic blocks may end on one
source line and that there is no simple mapping from numbered branch records
back to source constructs. Therefore the X25519MLKEM768 collector treats each
gcov arc as the coverage outcome and uses line-local pair ordinals only as a
stable wire encoding for the existing two-outcome receipt structure. It does
not claim MC/DC or reconstruct C boolean expressions. The four promotion-
critical SIMD predicates retain their explicit runtime decision IDs.
