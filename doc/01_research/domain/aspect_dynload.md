<!-- codex-research -->
# Aspect Dynamic Loading: Domain Research

**Date:** 2026-08-20  
**Method:** primary specifications and vendor/runtime documentation only.  
**Provenance:** highest-capability Codex completion audit
(`/root/audit_aspect_plan_completion`). Lower-model sidecars: **N/A**. No
production source, test, bootstrap, or Git action was performed.

## Dynamic call-site visibility

The Java runtime exposes two deliberately different update contracts.
`MutableCallSite` permits target changes whose visibility to other threads is
not immediate; `syncAll` is required when cross-thread publication matters.
`VolatileCallSite` makes every target read/write immediately visible but warns
of a performance penalty. `SwitchPoint` provides a one-way invalidation guard
that redirects future calls to a fallback. These are strong precedents for
making visibility and invalidation explicit rather than hiding them behind a
single “dynamic call” abstraction:

- [MutableCallSite](https://docs.oracle.com/en/java/javase/15/docs/api/java.base/java/lang/invoke/MutableCallSite.html)
- [VolatileCallSite](https://docs.oracle.com/en/java/javase/22/docs/api/java.base/java/lang/invoke/VolatileCallSite.html)
- [SwitchPoint](https://docs.oracle.com/en/java/javase/15/docs/api/java.base/java/lang/invoke/SwitchPoint.html)

**Implication for Simple:** a chosen facet/advice contract should name whether
updates are immutable-per-generation, eventually published with an explicit
barrier, or volatile on every dispatch. The cost belongs in the NFR contract.

## Loader lifetime and unload safety

POSIX defines `dlopen()` as returning a handle for symbol lookup and eventual
close; loading one object may also load its dependencies. `dlclose()` expresses
an application intent to release a handle, not a guarantee that the object is
immediately removed. After close, applications must assume resolved symbols are
unavailable, and an object with outstanding relocation dependencies cannot be
removed safely:

- [POSIX `dlopen`](https://pubs.opengroup.org/onlinepubs/009696799/functions/dlopen.html)
- [POSIX `dlclose`](https://pubs.opengroup.org/onlinepubs/9699919799.orig/functions/dlclose.html)

**Implication for Simple:** safe hot unload cannot be inferred from refcount
decrement alone. It needs generation-aware references and proof that no direct
or relocated reference can execute. Process-lifetime pinning is a valid smaller
contract and should be an explicit option.

## Once initialization and concurrency

Rust's standard `Once` specifies that concurrent callers block until the sole
initialization completes and that completion happens-before all returns.
`OnceLock::get_or_init` likewise permits many concurrent callers while allowing
only one initializer (absent panic). These contracts capture the minimum
observable behavior needed for one facet activation under contention:

- [Rust `Once`](https://doc.rust-lang.org/std/sync/struct.Once.html)
- [Rust `OnceLock`](https://doc.rust-lang.org/nightly/std/sync/struct.OnceLock.html)

**Implication for Simple:** the requirement must specify waiter behavior,
failure publication, retry policy, and a happens-before guarantee. A test
runner that executes tasks inline cannot provide evidence for that contract.

## Signed metadata and key lifecycle

The Update Framework defines a trusted root role, threshold signatures,
versions, expiry, consistent snapshots, and key rotation/revocation. Clients
begin with trusted root metadata; root keys are intended to be kept offline.
NIST SP 800-57 Part 1 treats key generation, storage, cryptoperiod, compromise,
revocation, and destruction as one lifecycle rather than a single verification
function:

- [TUF specification 1.0.26](https://theupdateframework.github.io/specification/v1.0.26/)
- [NIST SP 800-57 Part 1 Rev. 5](https://csrc.nist.gov/pubs/sp/800/57/pt1/r5/final)

**Implication for Simple:** a real pack-signing claim requires a build signer,
independently provisioned verification roots, key IDs/versions, rotation and
revocation behavior, and rollback protection. A content digest only proves
byte identity; it does not authenticate a publisher. Until custody exists,
signature verification should be explicitly disabled and fail closed when a
pack claims an unsupported signed profile.

## Zstandard dictionary compatibility and resource bounds

RFC 8878 specifies the zstd frame format. Its `Dictionary_ID` identifies the
dictionary needed to decode a frame, while dictionary material is distributed
out of band. Decoders may reject unsupported parameters and should impose
reasonable memory limits based on the advertised window. Frames are
independently decodable when their required dictionary is available:

- [RFC 8878: Zstandard Compression and the `application/zstd` Media Type](https://www.rfc-editor.org/rfc/rfc8878.html)

**Implication for Simple:** the pack format must bind dictionary ID and profile,
reject unknown dictionaries deterministically, cap declared/output sizes before
allocation, authenticate compressed bytes and metadata before decompression,
and test decompression bombs/truncation. “Supports zstd” without this profile is
not a complete compatibility or security contract.

## W^X and artifact replacement

The GNU C Library dynamic-linker hardening guidance rejects writable and
executable load segments and recommends installing an updated shared object at
a new path followed by an atomic rename instead of overwriting a mapped file in
place. It also notes consistency risks when multiple related objects are
updated separately:

- [glibc Dynamic Linker Hardening](https://www.sourceware.org/glibc/manual/latest/html_node/Dynamic-Linker-Hardening.html)

**Implication for Simple:** retain the RW-to-RX transition, never map pack code
RWX, and use immutable generation identities rather than a size-only cache key.
A complete multi-file pack should publish as one admitted generation.

## Performance evidence

Linux `/proc` documents `VmHWM` as peak resident set size and separates resident
anonymous, file, and shared-memory components; `/proc/<pid>/smaps` is more
precise but more expensive to read. Hyperfine's own documentation describes
warmups, multiple timed runs, cache-preparation commands, outlier detection, and
machine-readable export:

- [Linux proc filesystem documentation](https://docs.kernel.org/filesystems/proc.html)
- [Hyperfine documentation](https://github.com/sharkdp/hyperfine)

**Implication for Simple:** startup, hot-call, and RSS targets must name the
binary/source identity, fixture, warmup/cache state, sample count, percentile,
and measurement source. Error paths and interpreter-inline concurrency are not
substitutes for a successful admitted native path.

## Domain synthesis

The strongest common pattern is explicit phase and generation boundaries:
authenticate immutable bytes, decode within declared bounds, map W^X, relocate,
then atomically publish one generation through a once/happens-before edge.
Resident calls after publication should touch only memory. Updates or unloads
need a separate, costed visibility/quiescence policy. The feature and NFR
options translate these precedents into user-selectable Simple contracts; this
research intentionally does not select one.

