# SFFI Safety Census — 2026-08-25

**Revision:** `5e0af505385` plus the current dedicated-worktree change
**Command:** `SFFI_SOURCE_ONLY=1 sh scripts/audit/rt-safety-census.shs ...`
**Evidence bundle:** none supplied

This is a static source and provider inventory, not a safety certificate. The
census deliberately classifies every declaration as unsafe unless the complete
nine-input evidence bundle is freshly replayed and its provider-scoped Ed25519
signature, digests, ABI registry, artifact, compiler, and verification report
all pass admission. No such bundle was supplied, so the verified-and-signed
count is correctly zero.

## Current result

| Metric | Declaration rows | Distinct `rt_*` symbols |
|---|---:|---:|
| Total | 11,572 | 3,137 |
| Explicitly `@unsafe(... ffi ...)` | 2,857 | 1,793 |
| Contract documented | 1,044 | 398 |
| Cryptographically verified and signed | 0 | 0 |
| Untouched: no unsafe tag, contract, or evidence | 8,468 | 1,817 |
| Unsafe tag plus declared contract | 797 | 380 |
| Lexical unsafe minimization | not measured | not measured |
| Symbols with multiple source-signature hashes | — | 264 |

All 11,572 declaration rows remain fail-closed unsafe in the census. An unsafe
annotation is necessary migration metadata; it does not verify the ABI or the
provider implementation.

## Provider provenance and implementation languages

The declaration inventory assigns each distinct symbol to one provider class:

| Provider class | Distinct symbols |
|---|---:|
| Linked native implementation, language not proven | 1,286 |
| No implementation observed | 984 |
| Rust | 623 |
| C or C++ source-only provider | 244 |

The implementation-definition scan independently found:

| Language | Definitions | Distinct symbols | Files |
|---|---:|---:|---:|
| C | 2,405 | 1,901 | 90 |
| Rust | 2,146 | 2,124 | 173 |
| Simple | 671 | 646 | 64 |
| C++ | 219 | 219 | 1 |

These tables answer different questions. Provider provenance is conservative
per declared symbol; the definition scan counts every owned implementation and
therefore includes mirrors and alternative providers.

## Highest remaining debt

Production contains 5,397 declaration rows, of which 2,824 are untouched. The
largest untouched families are `rt_file` (2,529 rows), `rt_process` (966),
`rt_env` (388), `rt_time` (335), and `rt_dir` (217). Test declarations account
for another 5,154 untouched rows and must not be allowed to inflate production
confidence.

The 264 multi-signature-hash symbols are the first ABI-integrity triage set.
This scanner hashes normalized source declarations, so parameter spelling,
nullable surface syntax, and other source-shape differences can create variants
without proving distinct machine ABIs. Conversely, a matching source hash does
not prove provider layout or calling convention. Each candidate must therefore
be reconciled against compiler-resolved canonical types and provider metadata;
unsafe tagging alone cannot make a real conflict callable safely. After that
triage, migration should reduce production untouched rows through one canonical
owner per family, typed `Option`/`Result` contracts, and the smallest lexical
unsafe block.

## Performance and memory constraint

Migration must not add per-call hashing, signature checks, symbol discovery,
string or map lookup, locks, generic marshalling, or avoidable allocation and
copying. Evidence and ABI closure are checked once at admission. Hot calls use
an immutable typed slot plus only the status, null, sentinel, bounds, encoding,
and ownership checks required by that signature.

## Honest status

All SFFI is **not** safe and verified. Current source-only status is zero
verified-and-signed symbols, 8,468 untouched declaration rows, and 264 symbols
whose declarations have multiple source-signature hashes requiring resolved-
type triage. The remaining declarations must stay unsafe until exact provider
evidence and executable contracts prove a narrow safe wrapper.

The refreshed run was deliberately source-only because this sync lane was
instructed not to run builds or verification. Provider-class rows below retain
the prior full-backing scan and are not silently presented as refreshed.

## Post-census migration note — 2026-08-26

The bootstrap atomic family repaired 23 source/provider contracts instead of
mass-tagging the prior mismatched ABI. Ordering is no longer passed to SeqCst
providers, integer/boolean CAS now preserves real booleans in one call, and
flag inspection uses one non-mutating load. C, Rust, interpreter, and native
registries now close the new identities. Construction adds one non-positive
handle check; hot operations add no call, allocation, lookup, retry, hash, or
signature work. All raw declarations remain unsafe, the Rust provider remains
mutex/map-backed, and no artifact evidence was supplied, so signed/admitted
coverage remains zero.

The bootstrap sandbox builder removed seven unused raw declarations and tagged
and lexically confined its fifteen live reset/configure/apply calls. The
source-only delta is seven fewer rows, fifteen fewer untouched rows, and fifteen
more contract-declared unsafe rows. Runtime behavior and complexity are
unchanged: the builder still performs one mutation per configured scalar or
domain/path and one final checked apply. The exported transaction is tagged
unsafe because successful status does not prove rollback or provider identity.
Typed-native ABI entries, exact artifact evidence, and signatures remain
absent, so verified-and-signed stays zero and the headline census is not
rewritten without a fresh full run.

The backward-compatible `src/app/io/mod.spl` hub was narrowed without changing
its direct-call shape: one unused `rt_env_get` redeclaration was removed, two
dead nil checks now call the existing nullable `env_get_opt` owner, and all 11
remaining random/logging/volatile raw declarations and calls are explicitly
tagged and lexically confined. The new
`scripts/audit/app-io-hub-sffi-authority.shs` ratchets the declaration count,
owner calls, and no-extra-dispatch shape. This delta has not been used to
rewrite the baseline table above; a future full census must measure the new
global totals.

The canonical `std.nogc_sync_mut.io.env_ops` compatibility layer was then
narrowed: its duplicate `rt_env_get` declaration/calls now use
`io_runtime.env_get_opt`, and its `rt_env_vars` declaration was corrected from
an incompatible `Dict<text,text>` result to the provider's nullable tuple-array
representation. The snapshot remains explicitly unsafe because ownership and
allocation failure are not proven. No dictionary conversion was added, so the
fix removes a representation hazard without adding an allocation or copy.
`scripts/audit/env-ops-sffi-authority.shs` pins this shape.

The contained `io.sysinfo_ops` leaf now has checked `Result` APIs for PID,
hostname, and available parallelism. Non-positive integer sentinels and
nil/empty hostname results become typed errors. Existing infallible spellings
remain for compatibility but are explicitly unsafe and preserve their legacy
sentinels. Each provider is still called through one direct always-inline raw
owner; success adds only the required comparison/null check and allocates
nothing. `scripts/audit/sysinfo-ops-sffi-authority.shs` ratchets the shape.

The canonical sync/async `sffi.system` facade now mirrors the same contract:
home, environment-snapshot, and hostname raw returns are nullable; checked
`Result` APIs reject absence/allocation failure and non-positive PID/CPU
sentinels. Legacy total spellings retain their old empty/zero behavior only
behind explicit unsafe annotations. The existing system authority ratchet was
strengthened to pin these checked contracts and all direct lexical owners.

The extern-only `std.env.types` compatibility surface remains present because
the compiler has special import-registration handling for that module. All nine
raw exports are now explicitly FFI-unsafe, and nullable lookup/snapshot/home/
hostname provider results are typed accordingly. Seventeen direct call owners
across the sync and async variable/path/platform implementations confine the
raw operations. Both lanes expose a checked snapshot API; legacy list APIs are
explicitly unsafe when they collapse allocation failure to `[]`. No conversion,
lookup table, or dispatch layer was introduced.

The first `rt_file` slice corrected mmap-text nullability and added checked
size/SHA-256/mmap-text APIs. Most importantly, append no longer maps a failed
size lookup (`-1`) to offset zero and overwrites from the beginning; it returns
false before issuing a write. Each of the three providers has one direct
always-inline owner. The checked success paths add only sentinel/length/null
checks and no lookup or allocation.
### Directory-operation authority follow-up

The canonical `nogc_sync_mut.io.dir_ops` boundary now confines its four raw
directory calls to `@always_inline` lexical `unsafe(ffi)` owners.  Create and
remove operations retain their direct boolean status ABI with no new lookup,
allocation, copy, or dispatch.  The native walk compatibility API is tagged
unsafe because its current array-only return cannot distinguish provider
failure from a legitimate empty directory.  A static ratchet pins the owner
count and prevents raw calls from spreading outside those owners.
### File resource and mapping authority follow-up

The canonical file-operations compatibility module now confines raw file-lock
and memory-mapping calls to six always-inlined lexical `unsafe(ffi)` owners.
APIs that expose descriptors or process addresses are explicitly unsafe because
sentinel checking alone cannot prove address bounds, lifetime, mapping identity,
or exactly-once release.  The existing `SffiFileLock` resource wrapper remains
the safe lock path.  The change adds no registry lookup, allocation, copy,
hashing, or generic dispatch to these calls.
### JIT bridge single-owner follow-up

`app.io.jit_ffi` and `app.io.jit_sffi` were byte-identical 609-line modules,
including duplicate raw file-read and directory-create declarations.  The
former is now a seven-line compatibility re-export of the canonical
`jit_sffi` owner.  This removes duplicate SFFI authority and avoids parsing and
lowering a second implementation for legacy imports; it adds no runtime
dispatch, lookup, or copy.  The canonical owner itself now uses the typed
runtime file-result API and the shared directory owner, eliminating both local
raw declarations rather than merely relocating them.
### Process I/O file-authority follow-up

`app.io.process_ops` no longer declares its own raw file-read, positional-read,
or file-size symbols.  It uses the canonical nullable-result reader, signed
size owner, and checked positional reader.  Live process output still performs
one size query per stream per poll and reads only the newly appended suffix, so
the prior O(total-output) quadratic regression remains excluded.  The change
adds no extra existence probe, second read, registry lookup, or generic
dispatch.
### CLI file/path authority follow-up

`app.io.cli_ops` no longer declares raw absolute-path, file-read, or positional
write symbols.  File reads use the canonical nullable-result owner, writes use
the shared positional owner in a lexical unsafe scope, and path resolution uses
the shared path owner while retaining the legacy empty failure sentinel
internally.  CLI copy remains one source read and one destination write, with
no read-back, extra filesystem probe, registry lookup, or generic dispatch.
### Binary-file authority follow-up

`app.io.binary_file_ops` no longer declares `rt_file_write_bytes`; it delegates
to the canonical runtime byte-write owner.  The facade still performs one
direct byte-array write and returns the provider's boolean status, with no
array conversion, copy, retry, lookup, or generic dispatch.
### Launch-metadata admission follow-up

The launch-metadata checker no longer declares raw text or byte readers.  A new
canonical `file_read_bytes_result` preserves nullable provider failure without
a second read, and metadata selection now returns `Result<LaunchMetadata,
text>`.  Explicit sidecar, default sidecar, native trailer, and content-hash
reads fail closed rather than parsing or hashing fabricated empty input.  Each
selected input is still read once; no retry, read-back, lookup, or generic
dispatch was added.
### Simple Portal authority follow-up

The Simple Portal content database and server no longer declare raw file-read
or directory-create symbols.  Database startup now performs four typed reads
instead of four existence probes plus four reads, reducing syscall work while
failing closed.  Static serving rejects provider read failure rather than
hashing and serving fabricated empty content, and playground audit-directory
creation failure is no longer ignored.  No retry, read-back, registry lookup,
or generic dispatch was added.
### Release-installer authority follow-up

The release installer no longer declares raw byte-read or directory-create
symbols.  Font and notice hashing uses typed one-read results, every directory
creation and source/library/header copy is checked, and the installer cannot
print success after a partial copy.  Hash helpers still read each selected file
once; no retry, read-back beyond the existing post-copy integrity check,
registry lookup, or generic dispatch was added.
### Package-manifest authority follow-up

Package manifest parsing and add/remove mutation paths no longer use a local
raw text reader or existence-then-read pairs.  Each path performs one typed
read, distinguishes provider failure from a valid empty file, and returns
before parsing or mutation on failure.  This removes filesystem probes rather
than adding retries, copies, registry lookups, or generic dispatch.
### Package-resolver authority follow-up

The dependency resolver no longer declares or calls a raw manifest reader.
Absent optional dependency manifests retain the `0.0.0` default, but a present
manifest now uses one typed read and propagates empty, unreadable, or malformed
metadata as a resolution error instead of silently installing with fabricated
version data.  Dependency traversal remains linear and adds no retry, second
read, registry lookup, or generic dispatch.
### Package-lock authority follow-up

Package lock loading no longer declares a raw text reader or collapses every
failure to “no lock.”  Its type is now `Result<LockFile?, text>`: absence is
`Ok(nil)`, while present-but-unreadable, empty, or malformed files are errors.
Frozen and ordinary installs both stop on those errors.  Optional-file loading
remains one existence probe plus one read, with no retry, second read, lookup,
or generic dispatch.
### Package CLI authority follow-up

The package CLI no longer declares a raw manifest reader.  Dry-run JSON uses
one typed read instead of an existence/read pair and fails before reporting
counts when the provider read fails.  Its previously nested CLI-argument extern
is now an explicit `unsafe(ffi)` declaration reached through one always-inlined
lexical owner.  No retry, second read, lookup, copy, or generic dispatch was
added.
### C-runtime source authority follow-up

The C code generator no longer declares a raw runtime-source reader or performs
an existence/read pair.  It makes one typed read, returns non-empty runtime
source, and explicitly logs missing/unreadable or empty input before selecting
the pre-existing embedded fallback.  Provider failure can no longer become
silent empty C code.  The change removes one filesystem probe and adds no
retry, copy, lookup, or generic dispatch.
### Compiler source-file authority follow-up

The compiler-common `SourceFile.load` boundary now declares the provider's
nullable text result accurately, tags it `unsafe(ffi)`, and confines the raw
call to one always-inlined lexical owner.  Provider `nil` and an existing empty
source are diagnosed separately.  Loading still performs one read and coverage
identity reuses the lifted content; no probe, retry, copy, lookup, or generic
dispatch was added.
### Compiler source-pipeline authority follow-up

The phase-1 bootstrap source loader now declares its raw file result nullable,
tags it `unsafe(ffi)`, and confines it to one always-inlined lexical owner.
Provider `nil` now fails the load instead of being treated as an intentionally
empty file; the pre-existing empty-file skip remains.  The streaming and
closure traversal still perform one read per selected bootstrap file, with no
probe, retry, copy, lookup, or generic dispatch added.
### Compiler public-header authority follow-up

Public-header generation now tags all six raw process/file/directory/path
declarations `unsafe(ffi)` and confines each to one always-inlined lexical
owner.  Source reads are nullable, boolean and exit statuses remain checked,
and empty joined-path sentinels fail before writes.  The hot path retains the
same foreign-call count and adds no lookup, allocation, copy, hash, or generic
dispatch.
### Compiler public-process authority follow-up

The lightweight public compile-process facade now tags its three raw process,
existence, and read declarations `unsafe(ffi)` and confines them to three
always-inlined lexical owners.  SDN reads are nullable; subprocess exit codes
and generated-output presence remain mandatory checks.  Raw calls remain
one-for-one, with no extra process, filesystem probe, allocation, copy, lookup,
or generic dispatch.
### Compiler public-VHDL authority follow-up

The public VHDL compile facade now declares its source-map reader nullable,
tags it `unsafe(ffi)`, and confines it to one always-inlined lexical owner.
After a successful external compile, source or generated-output read failure
now changes the result to a typed runtime error instead of writing an empty
source map and returning success.  The successful branch retains exactly two
reads and adds no probe, retry, copy, lookup, or generic dispatch.
### Compiler interpret-cache authority follow-up

The public interpret API now tags its SMF existence and live-source read
dependencies `unsafe(ffi)` and confines them to two always-inlined lexical
owners.  A nullable source-provider failure produces a conservative cache miss
before interface/hash comparison, while valid empty source remains distinct.
Cache admission retains one existence query and one source read, with no retry,
copy, lookup, hash duplication, or generic dispatch added.

### Compiler plugin-startup authority follow-up

Plugin startup now represents manifest-read and home-directory provider failure
as nullable text and confines both raw runtime calls to always-inlined lexical
owners.  An unavailable home directory omits only the user-global discovery
path; an unreadable manifest is skipped, while a valid empty manifest remains
a successful empty input rather than a fabricated provider result.  Discovery
retains one home lookup and one read per candidate manifest, with no added
probe, retry, allocation, copy, lookup, lock, or generic dispatch.

### Compiler MDSOC-config authority follow-up

The MDSOC manifest loader now declares its raw file-read result as nullable and
confines the call to one always-inlined lexical `unsafe(ffi)` owner.  Provider
failure remains a typed absence at the boundary and is mapped to the loader's
existing `nil` result; a valid empty manifest follows the same documented empty
configuration path.  The loader retains exactly one read with no extra probe,
retry, allocation, copy, lookup, lock, hash, or generic dispatch.

### Compiler cache file-stamp authority follow-up

The file-stamp cache now confines its four raw filesystem calls to
always-inlined lexical `unsafe(ffi)` owners.  Its SHA-256 result is correctly
nullable, and the measurement path rejects nil digests, negative sizes, and
the runtime's actual zero mtime failure sentinel before constructing a stamp.
The successful fast path retains the same existence/size/mtime probes, and the
torn-read path retains the same metadata/hash call counts; no allocation,
copy, lookup, lock, extra I/O, or generic dispatch was added.

### Compiler cache-limits authority follow-up

Cache-limit loading no longer declares or calls `rt_env_get` directly.  It now
uses the canonical nullable `std.io_runtime.env_get_opt` facade, removing this
module's unsafe authority rather than duplicating it behind another wrapper.
The startup path retains one environment lookup and the same parse/default
logic, with no additional scan, allocation, copy, lock, retry, or dispatch
table.

### Compiler DI authority follow-up

The compiler dependency-injection container no longer owns a raw `rt_env_get`
declaration or call.  Both system-test lock checks now use the canonical
nullable `std.io_runtime.env_get_opt` facade, eliminating local unsafe
authority.  Short-circuit behavior is unchanged: the DI bypass variable is
queried only when system-test mode is enabled, so there is no added environment
lookup, allocation, copy, cache, lock, or dispatch table.

### Shared compiler-config authority follow-up

The shared low-layer compiler configuration module retains its single required
raw environment declaration, now tagged `unsafe(ffi)` and reachable only
through one always-inlined lexical owner.  Its nullable result contract already
matches provider absence.  All configuration consumers keep the same one-call
lookup behavior, with no added allocation, copy, cache, lock, hash, or dispatch
table.

### Native-build cache environment authority follow-up

The native-build cache entrypoint no longer declares or calls `rt_env_get`
directly.  Cache-root selection now uses the canonical nullable
`std.io_runtime.env_get_opt` facade, while cache probes use the canonical
always-inlined `file_exists` facade.  The unused local clock declaration was
also removed, leaving this module with no raw SFFI authority.
Each build invocation retains exactly one environment lookup and the same
default-directory branch, with no extra filesystem probe, allocation, copy,
cache, lock, hash, or dispatch table.

### MSVC linker authority follow-up

The MSVC linker no longer declares or calls raw process, filesystem, or
environment SFFI.  It uses the canonical `process_run`, always-inlined
`file_exists`, and nullable `env_get_opt` facades.  A missing
`ProgramFiles(x86)` value now omits that derived `vswhere.exe` candidate instead
of fabricating a path.  Discovery performs at most one environment lookup and
retains the same process invocations.  It probes the fixed path first, avoiding
a temporary candidate array and skipping the environment lookup and derived
probe when the fixed path exists; no cache, lock, hash, or dispatch table was
added.

### Backend interpreter authority follow-up

The tree-walking backend interpreter no longer declares raw environment SFFI;
its trace and strict-memory checks use the canonical nullable `env_get_opt`
facade, now always-inlined to preserve hot trace-probe cost.  Its three enum
discriminant sites share one always-inlined lexical `unsafe(ffi)` owner while
preserving the existing declaration type and runtime ABI.  Environment lookup
frequency and discriminant call counts remain unchanged, with no cache,
allocation, copy, lock, hash, boxing, or dispatch table added.

### LLVM target-selection authority follow-up

LLVM target selection no longer declares or calls raw environment SFFI.  Both
target-policy reads use the canonical nullable, always-inlined `env_get_opt`
facade, removing the module's local unsafe authority.  The two entrypoints keep
their existing single lookup and normalization work, with no cache, allocation,
copy, additional host probe, lock, hash, boxing, or dispatch table added.

### Shared backend-helper authority follow-up

Shared backend helpers no longer declare or call raw environment or AVX2 SFFI.
Their five configuration reads use the canonical nullable, always-inlined
`env_get_opt` facade, and the host capability query uses the canonical
always-inlined `std.simd.has_avx2` owner.  Call-site frequency and target-option
construction remain unchanged, with no cache, allocation, copy, extra CPUID,
lock, hash, boxing, or dispatch table added.

### MIR target-context authority follow-up

The MIR target-context provider no longer declares or calls raw environment
SFFI.  Both target reads use the canonical nullable, always-inlined
`env_get_opt` facade, eliminating local unsafe authority while retaining the
provider's uncached semantics.  Each entrypoint keeps one lookup and the same
trim/lower normalization, with no allocation beyond the existing normalized
text, extra host/tool probe, cache, lock, hash, boxing, or dispatch table.

### LLVM IR-builder environment authority follow-up

The LLVM IR builder no longer declares or calls raw environment SFFI.  Its
target reads use the canonical nullable, always-inlined `env_get_opt` facade,
preserving the existing fresh-read target-header behavior and lookup count.
The four opaque string-builder declarations remain explicitly tagged unsafe:
provider inspection confirms zero/new, zero/push, nil/finish, and negative/len
failure contracts that are not yet fully checked.  No per-line branch,
allocation, copy, cache, lock, hash, boxing, or dispatch was added in this slice.

### Compiler pass-receipt authority follow-up

Pass-receipt emission no longer declares or calls raw environment or append
SFFI.  It uses canonical nullable `env_get_opt` and always-inlined
`file_append_text` facades.  When a sink is configured, a false append status
now raises `E-SFFI-014` instead of silently returning a receipt line that was
not persisted.  The path retains one lookup and one append, adding only the
mandatory status branch with no retry, extra I/O, allocation, copy, cache,
lock, hash, boxing, or dispatch table.

### Public driver API-types authority follow-up

The tier-0 driver API-types module removed seven unused raw declarations that
downstream modules do not consume from it.  Its two real dependencies—nullable
runtime-path environment lookup and runtime-library candidate existence—remain
behind two always-inlined lexical `unsafe(ffi)` owners because the layer cannot
import the higher I/O facade.  Runtime discovery retains one environment lookup
and the same ordered candidate probes, with no additional allocation, copy,
filesystem call, cache, lock, hash, boxing, or dispatch table.

### AOT driver-pipeline authority follow-up

The AOT pipeline no longer declares or calls raw environment, source-read, or
text-hash SFFI.  It uses canonical `env_get_opt`, typed `file_read_result`, and
always-inlined `hash_text` facades.  An unreadable source in the combined
native+SMF output path now returns a compile error instead of hashing fabricated
empty text into a successful manifest.  The successful path retains nine
environment lookups, one source read, and one hash; failure adds no retry or
extra I/O, and no cache, lock, boxing, or dispatch table was introduced.

### AOT VHDL-output authority follow-up

AOT VHDL output no longer declares raw environment SFFI; trace policy uses the
canonical nullable, always-inlined facade.  Discriminant and payload calls are
confined to two always-inlined lexical owners, and payload lifting now occurs
only after the result tag is proven `Ok` or `Err`.  Canonical tags are computed
once and reused, so the entry and catalog checks retain four total discriminant
calls while corrupt tags fail with `E-SFFI-017`.  No allocation, copy, cache,
lock, hash, boxing, extra payload call, or dispatch table was added.

### Shared module-path naming authority follow-up

Shared module-path naming no longer declares or calls raw `rt_string_len`.
Its substring-position helper now uses the canonical text `index_of` operation
directly and maps absence to the existing `-1` sentinel.  This removes the
previous `contains` scan, split-array allocation, prefix-text allocation, and
foreign length dispatch while preserving empty-needle and not-found behavior.

### Frontend trace-policy authority follow-up

Frontend trace policy no longer declares or calls raw `rt_env_get`; both trace
reads use the canonical nullable, always-inlined environment facade.  The
outer-scope snapshot still performs one lookup and nested scopes perform none,
while an unscoped query retains one lookup.  Its packed scalar state remains
allocation-free, with no added cache, lock, copy, hash, boxing, or dispatch.

### Frontend registry-promotion authority follow-up

Aspect, effect, layer-equivalence, and RT-criticality registries now tag their
raw transient-owner promotion declaration `unsafe(ffi)` and confine calls to
one always-inlined lexical owner per module.  The foreign result remains a
boolean and every existing failure check is preserved; no numeric workaround
or fabricated success was introduced.  Promotion counts and eager/short-circuit
evaluation shapes are unchanged, and registry lookup paths gain no foreign
call, allocation, copy, cache, lock, hash, boxing, or dispatch table.

### HIR lowering types authority follow-up

HIR lowering types no longer declares raw environment SFFI; its shared
nullable helper delegates to canonical always-inlined `env_get_opt`.  Enum
discriminant, heap-reference formation, and transient diagnostic promotion are
tagged `unsafe(ffi)` and confined to existing or new always-inlined scalar
owners.  Diagnostic promotion still evaluates all three parallel owners and
returns their boolean conjunction; the driver still fails closed on false.
No call-count, allocation, copy, cache, lock, hash, boxing, or dispatch-table
change was introduced.

### Header shared-library flags authority follow-up

Shared-library flag generation no longer declares or calls raw `rt_env_get`.
Its local nullable helper delegates to canonical always-inlined `env_get_opt`.
MinGW detection retains exactly the existing `MSYSTEM` lookup followed, when
needed, by `SIMPLE_LINKER_FLAVOR`; platform process probes are unchanged.  No
new allocation, copy, cache, lock, hash, boxing, subprocess, or dispatch was
introduced.

### MIR optimizer environment-authority follow-up

The MIR optimizer no longer declares or calls raw `rt_env_get`; its shared
nullable helper delegates to canonical always-inlined `env_get_opt`.  Trace and
bootstrap policy remain mutation-visible at their existing query sites, while
verify-each retains its one-read process cache.  No environment read, pass-loop
work, allocation, copy, lock, hash, boxing, or dispatch was added.

### MIR bulk-ops flag spec authority follow-up

The quarantined bulk-ops behavioral spec no longer declares or calls raw
`rt_env_set`; setup uses canonical `env_set`.  Each of its three
boolean setter results is now asserted before optimizer behavior is inspected,
so a failed environment mutation cannot fabricate a passing disabled-path test.
This changes test setup only and adds no compiler-runtime or optimizer hot-path
work.

### Compiler performance-clock authority follow-up

Profiler, trace, and benchmark tools now tag monotonic-clock declarations
`unsafe(ffi)` and confine them to file-local always-inlined owners.  Benchmark
timestamp text is likewise explicitly unsafe-minimized because its provider is
not status-bearing, signed, or admitted.  Every sampling site retains exactly
one direct clock call; no validation branch, allocation, copy, cache, lock,
hash, formatting step, lookup, boxing, or dispatch table was added to timing
paths.

### Compiler performance CLI authority follow-up

The performance command and standalone optimizer no longer declare or call
raw `rt_get_args`; each imports the canonical CLI owner, whose argument-array
provider remains explicitly unsafe and unsigned.  Both entrypoints retain one
startup argument fetch.  No benchmark sample, project scan, allocation, copy,
cache, lock, hash, lookup, boxing, or dispatch work was added.

### SSA and AOP environment-authority follow-up

Variable-reassignment SSA and driver AOP weaving no longer declare or call raw
`rt_env_get`; both use canonical nullable `env_get_opt`.  SSA deliberately
retains its two mutation-visible debug checks on the multi-block materialization
path, while AOP retains two boolean and two level reads per weave.  No caching,
allocation, copy, lock, hash, boxing, extra provider call, or dispatch table was
introduced.

### Duplicate-check scalar math authority follow-up

Duplicate-check math now tags raw square root `unsafe(ffi)` and confines it to
the existing `math_sqrt` helper, which is always-inlined.  Dense cosine
similarity routes both magnitude roots through that owner and still performs
exactly two scalar provider calls after its single O(n) accumulation loop.  No
validation branch, allocation, copy, cache, lock, hash, lookup, boxing, or
dispatch table was added.

### Duplicate-check detector-path authority follow-up

Duplicate-check file discovery now declares path canonicalization nullable,
tags it `unsafe(ffi)`, and confines its sole call to an always-inlined owner.
Null or empty canonicalization fails closed before directory walking instead of
becoming a fabricated path.  Successful directory discovery retains one path
call and one walk with unchanged filtering; no retry, extra traversal,
allocation, copy, cache, lock, hash, lookup, boxing, or dispatch was added.

### Tiered-JIT authority follow-up

Tiered JIT management removed one unused raw call-signature declaration and
now confines its seven live JIT/clock primitives to always-inlined lexical
`unsafe(ffi)` owners.  Lazy creation, two compile timing reads, compilation,
native calls, presence checks, and cleanup retain their exact provider-call
counts.  No per-call admission, signature, hash, lookup, allocation, copy,
cache, lock, boxing, generic marshalling, or additional dispatch was added.
Compile error text is now nullable at the raw boundary; null becomes an
explicit `E-SFFI-017` error on the cold promotion path, while empty text remains
the provider's valid success result.
The provider remains unsigned and unverified, so this is unsafe minimization,
not safe promotion.

### MIR interpreter async-runtime authority follow-up

The MIR interpreter now tags actor spawn/send/receive and scheduler yield
`unsafe(ffi)` and confines all four primitives to always-inlined lexical
owners.  Runtime-name dispatch, argument checks, receive timeout behavior, and
provider-call counts are unchanged; no scheduler lookup, allocation, copy,
cache, lock, hash, boxing, generic marshalling, or extra dispatch was added.
The dispatcher still returns legacy integer zero for malformed spawn/send
argument lists, so it remains explicitly unsafe pending a `Result` migration
through MIR instruction execution and is not verified or signed.

### MIR interpreter core authority follow-up

The core MIR interpreter no longer declares or calls raw environment lookup;
strict and ExecIR policy retain one canonical nullable read each during
interpreter construction.  Its three unknown-value diagnostic probes now use
one always-inlined lexical discriminant owner.  Normal instruction, constant,
and binary-operation dispatch gains no call, branch, allocation, copy, cache,
lock, hash, lookup, boxing, marshalling, or dynamic dispatch work.

The feature-vector builder no longer imports or calls the raw square-root
symbol from `math_utils`; it consumes the confined always-inline owner.  Its
shape remains one root after one O(n) frequency-weight accumulation, with no
additional traversal or temporary collection.

### MDSOC module-storage contract follow-up

`ModuleStoragePort` now requires `fn(text) -> Result<text,text>` instead of an
untyped callback whose contract fabricated empty text on failure.  Disk storage
delegates once to typed `file_read_result`; memory storage returns `Ok(source)`
for registered values, including empty text, and `Err` for absence.  The port
has no current consumers, so the contract was corrected before runtime fan-out.
There is no extra file read, registry scan, copy, cache, lock, hash, lookup,
boxing layer, or dynamic dispatch.

### Duplicate-check incremental-write authority follow-up

Incremental duplicate-check caching no longer declares or calls raw
`rt_file_write_text`; after its existing parent-directory creation and single
serialization, it calls canonical `file_write_exact`.  The success path retains
one write and the caller still reports false status.  No retry, metadata probe,
extra serialization, allocation, copy, cache, lock, hash, lookup, boxing, or
dispatch table was added.

### MDSOC layer-document read authority follow-up

The layer documentation checker no longer declares or calls non-null raw
`rt_file_read_text`.  Its four existing reads use typed `file_read_result`;
provider failure now returns each query's conservative failure state instead of
fabricating empty text, while a valid empty file remains `Ok("")`.  The slice
preserves read counts and search complexity.  Each existing read gains one
bounded typed-result lift outside inner scan loops; there is no retry, extra
traversal, file-buffer copy, cache, lock, hash, lookup, or dynamic dispatch.

### Builtin type-registry authority follow-up

Builtin type lookup and membership now tag their two raw provider declarations
`unsafe(ffi)` and confine each to an always-inlined lexical owner. Lookup
remains nullable and membership remains boolean: no nil, empty-text, or numeric
substitution was introduced. Each query retains exactly one direct provider
call and adds no hashing, signature check, map, cache, lock, allocation, copy,
boxing, generic marshalling, or dynamic dispatch. Because nil/false still
cannot distinguish ordinary absence from provider failure, the provider remains
unsafe, unsigned, and unverified rather than being promoted as safe.

### SIMD capability authority follow-up

SIMD target detection now tags ten CPUID, auxiliary-vector, sysctl, RISC-V,
architecture-gate, and CUDA primitives `unsafe(ffi)` and confines each to an
always-inlined direct owner. The architecture dispatch, three x86 CPUID reads,
two Linux HWCAP reads, two Apple sysctl reads, conditional RISC-V reads, and
single CUDA query retain their existing call counts and scalar sentinel
semantics. The two raw file-read declarations were removed; SVE length and
`/proc/cpuinfo` now use one typed read each and preserve the existing empty or
zero capability fallback on provider failure. These are detection-time paths,
not vector inner loops, and no retry, extra scan, hash, signature check, cache,
lock, generic marshalling, or dynamic dispatch was added. Sentinel-bearing
providers remain explicitly unsafe, unsigned, and unverified.

### MIR statement-lowering authority follow-up

MIR statement lowering removed an unused raw dictionary declaration and its
duplicate raw environment declaration. Its two debug gates now use the
canonical nullable environment facade with the same one-read behavior at each
existing call site. Tagged statement discriminant and payload projections are
tagged `unsafe(ffi)` and confined to always-inlined lexical owners; the payload
contract is now nullable and the existing expression-statement path rejects
nil before lowering it. Direct projection counts and statement dispatch
complexity are unchanged, with no admission, hash, cache, lock, allocation,
copy, boxing, generic marshalling, or additional dynamic dispatch. The tagged
runtime provider remains unsafe, unsigned, and unverified.

### MIR function/type-lowering authority follow-up

MIR function and type lowering now tags its sole tagged-value discriminant
primitive `unsafe(ffi)` and confines all 22 existing projections to one
always-inlined lexical owner. GPU parameter classification, dictionary/named/
optional type predispatch, inner optional diagnostics, and the unreachable-type
diagnostic preserve exactly the same projection and branch counts. No cache,
hash, signature check, lookup, lock, allocation, copy, boxing, generic
marshalling, or extra dynamic dispatch was added. The raw discriminant provider
remains explicitly unsafe, unsigned, and unverified.

### MIR bootstrap process-authority follow-up

MIR bootstrap global and type registration removed two duplicate raw process
exit declarations and now use the canonical exit owner at all twelve existing
fatal sites. A raw string-length declaration and its unused split-based text
index helper were deleted rather than wrapped. Normal bootstrap and lowering
paths gain no call or branch, while fatal paths retain one exit call each; the
dead helper removal also eliminates a latent two-scan split/allocation path.
No admission, hashing, signature check, cache, lock, lookup, boxing, generic
marshalling, or extra dispatch was added. This centralizes unsafe authority but
does not make the underlying runtime provider signed or verified.

### MIR module-lowering environment authority follow-up

MIR module lowering removed its duplicate raw nullable environment declaration
and retains one always-inlined local helper through canonical `env_get_opt`.
The three trace gates and bootstrap-mode gate keep exactly four startup/lowering
reads and the same disabled fallback for unset or empty values. No read moved
into a loop and no cache, allocation, copy, hash, signature check, lock, lookup,
boxing, generic marshalling, or extra dispatch was added. The canonical owner
still represents a raw, unsigned, unverified provider; this slice removes
duplicate authority rather than promoting environment input as verified.

### MIR literal-lowering dead-authority follow-up

MIR literal lowering removed three unused raw dictionary, environment, and
tagged-discriminant declarations. The module had no call sites for any of them,
so no wrapper or replacement authority was introduced. Generated MIR, loop and
dispatch complexity, call counts, branches, allocations, copies, caches, locks,
hashes, lookups, boxing, and marshalling are unchanged; the module now exposes
no raw `rt_*` declaration at all.

### MIR method-lowering authority and trace-cost follow-up

MIR method lowering removed an unused raw dictionary declaration and its
duplicate raw environment declaration. The two live HIR type discriminant
projections are tagged `unsafe(ffi)` and confined to one always-inlined lexical
owner. Three dictionary-element and five conversion-log gates now share two
process-lifetime tri-state caches, matching the module's existing method-trace
policy: each flag performs at most one nullable provider read instead of one
read per qualifying method path, then uses one integer branch. Default-off and
boolean behavior are preserved without numeric API substitution. No allocation,
copy, hash, signature check, lock, lookup, boxing, generic marshalling, or extra
dynamic dispatch was added. The discriminant/environment providers remain
unsafe, unsigned, and unverified.

### MIR data environment-authority follow-up

MIR data and builder infrastructure removed its duplicate raw non-null
environment declaration and all five local unsafe blocks. Its three outer-scope
trace reads, three fallback trace reads, bootstrap gate, and builder-finalize
gate now use canonical always-inlined nullable `env_get_opt`; the existing
outer-scope cache and all eight call sites are unchanged. Unset and empty values
remain disabled. No read moved into a loop and no allocation, copy, cache, hash,
signature check, lock, lookup, boxing, generic marshalling, or dispatch was
added. The canonical runtime provider remains raw, unsigned, and unverified.

### MIR switch/operator environment-authority follow-up

MIR switch/operator/call lowering removed its duplicate raw nullable
environment declaration and retains its always-inlined `_sffi_env_get` helper
through canonical `env_get_opt`. The five default-padding, bootstrap, safety-
profile, and borrow-reference reads remain at their exact call sites with the
same nullable/default behavior. The existing cross-lane audit now requires the
canonical environment owner while continuing to pin all 16 discriminant
projections and five environment queries. No call, branch, allocation, copy,
cache, hash, signature check, lock, lookup, boxing, marshalling, or dispatch was
added. The remaining tagged-value provider is unsafe, unsigned, and unverified.

### MIR expression-dispatch environment-authority follow-up

MIR expression dispatch removed its duplicate raw nullable environment
declaration and collapsed its two-wrapper environment chain into one
always-inlined `mir_expr_env_get` owner over canonical `env_get_opt`. Its six
garbage, strict-array, field, bounds, and bootstrap query sites remain unchanged,
as does the existing garbage-trace cache. The cross-lane audit now rejects raw
environment authority while continuing to pin 95 discriminant, six payload,
and fourteen tuple projections. This removes one potential call layer and adds
no call, branch, allocation, copy, cache, hash, signature check, lock, lookup,
boxing, marshalling, or dispatch. Tagged providers remain unsafe and unverified.

### Admission identity join hardening

The contract inventory previously retained the admitted provider identity but
joined cryptographic admission to source declarations by symbol name alone.
That could mark a same-named declaration with a different canonical ABI
signature as reverified. Admission rows now retain `(symbol,
source_signature_sha256, provider_id)`, require an owned declaration with the
same symbol/signature pair, and join `reverified` only on that pair. A stale or
wrong-signature receipt fails closed instead of upgrading unrelated source.
This is census-only logic with no compiler, loader, or runtime-path cost.
Provider-to-artifact closure remains a separate admission requirement; source
annotations alone are still never treated as signed evidence.

### Frontend parse-cache authority follow-up

The frontend parse cache removed nine raw environment, file, directory,
process-id, hash, move, and delete declarations. It now uses canonical owners
while preserving four configuration reads, two existence probes, one exact
non-shelling hash, one typed read, one exact write, one move, and at most one
failed-move cleanup. Provider failure remains a cache miss; invalid hashes
remain empty keys; invalid process identity fails closed before temp-file
publication. The canonical hash owner performs the sole 64-byte validation, so
no second digest check or shell fallback was added. Disk I/O counts, cache
complexity, and stored data layout are unchanged, with no new scan, retry,
allocation, copy, lock, lookup, generic dispatch, or per-hit admission work.

### Driver action-index authority follow-up

The driver action index removed eight raw file, directory, process-id, and
clock declarations. It now uses canonical owners while preserving one
existence probe and typed read per lookup, two directory creates, one validated
PID and timestamp, one exact write, one move, and one failed-move cleanup per
publication attempt. Read failure and malformed data remain misses; write or
move failure remains a conflict and retains the existing lost-race re-read.
There is no extra retry, file scan, serialization, allocation, copy, cache,
hash, signature check, lock, lookup, boxing, marshalling, or dynamic dispatch.
PID/clock provider failures now fail closed rather than naming a fabricated
temporary file.

### Frontend trace environment-authority follow-up

The frontend runner removed its duplicate raw environment declaration and now
uses one always-inlined process-lifetime tri-state gate for
`SIMPLE_COMPILER_TRACE`. The two former provider reads per parsed module become
at most one nullable provider read per process followed by integer branches.
Both existing trace receipts remain boolean and default-off. No parsing loop,
source scan, allocation, copy, cache lookup, hash, signature check, lock,
boxing, marshalling, or dynamic dispatch was added; repeated module parsing
strictly loses environment-provider work.

### C-import header-read authority follow-up

C-import processing removed its raw non-null file-read declaration and changed
the private header reader to `Result<text,text>` through canonical
`file_read_result`. Provider failure now follows the existing explicit
`failed to read header` error path instead of first fabricating empty text;
successful empty content retains the existing empty-header rejection. Each
import still performs exactly one read and one bounded result lift before C
parsing, with no retry, extra scan, allocation, copy, cache, hash, lock, lookup,
boxing, marshalling, or dynamic dispatch.

### Lazy module-loader authority follow-up

The lazy interpreter module loader removed raw file-read and environment
declarations. `_lazy_try_read` now returns `Result<text,text>` through canonical
`file_read_result`; unreadable and empty candidate sources remain explicit
fallback conditions rather than fabricated successful text. The lazy-mode flag
still reads once, and `SIMPLE_LIB` now uses a resettable process-state cache so
candidate construction performs at most one provider read between loader
resets. Each requested candidate still receives at most one file read and the
outline scanner runs once on the selected source. No additional directory
search, source scan, allocation, copy, hash, signature check, lock, lookup,
boxing, generic marshalling, or dynamic dispatch was added.

### Interpreter CLI argument authority follow-up

Interpreter CLI declaration evaluation removed its duplicate raw
`rt_cli_get_args` declaration and now obtains arguments once through canonical
`std.io_runtime.get_args`. Native and Rust runtimes already alias
`rt_cli_get_args` and `sys_get_args` to the same argument storage. The parser
retains one `[text]` fetch, the same program/script-prefix skip, and the same
single pass that builds `argv`; no numeric substitution, second fetch, scan,
allocation beyond the existing argv copy, cache, hash, lock, lookup, boxing,
marshalling, or dynamic dispatch was added.

### Interpreter JIT state authority follow-up

The file-backed interpreter JIT removed four raw file and PID declarations and
now uses canonical typed read, exact write, delete, and validated PID owners.
Every existing state load, save, and cleanup retains one provider operation;
read failure still selects the default disabled state and no retry, metadata
probe, allocation, copy, cache, hash, lock, lookup, boxing, marshalling, or
dynamic dispatch was added. Source inspection also exposed pre-existing
multiple state-file reads/writes during `jit_record_call`; that hot-path design
debt is recorded separately and was not hidden behind an unmeasured cache.

### Core interpreter module-loader authority follow-up

The core interpreter module loader removed raw environment and file-read
declarations plus an unused raw path-join declaration. Its three parse/register/
load entrypoints now perform one typed `file_read_result` each and retain the
same empty-source rejection, depth restoration, and parse path. GC-family
warning tracing now uses one always-inlined tri-state environment gate reset by
the existing `module_loader_init`, reducing repeated provider reads without
changing warning behavior. No extra path normalization, candidate search, file
read, source scan, allocation, copy, hash, signature check, lock, lookup,
boxing, marshalling, or dynamic dispatch was added.

### Interpreter declaration-profile authority follow-up

Interpreter declaration evaluation removed its raw non-null environment
declaration and now seeds the assurance profile once through canonical nullable
`env_get_opt`. Unset, explicitly empty, and provider-failure states retain the
same default-profile input, while callers can still reapply an already resolved
policy later. Initialization retains exactly one read and one policy application
with no loop work, allocation, copy, cache, hash, signature check, lock, lookup,
boxing, marshalling, or dynamic dispatch added.
## 2026-08-26 module-resolution environment authority follow-up

`module_loader_resolve.spl` no longer redeclares `rt_env_get`; `SIMPLE_LIB` is
read through the canonical always-inline `env_get_opt` owner. The two raw path
ABIs remain locally confined so candidate ordering and all path-operation call
sites are unchanged. This slice is source-reviewed but unverified.
## 2026-08-26 lexer nullable-environment authority follow-up

The compiler lexer no longer redeclares `rt_env_get`. Its thirteen read call
sites use the canonical always-inline `env_get_nullable` transport, which keeps
explicitly empty values distinct from nil and remains one direct ABI call.
Write, file-read, and array-release ownership is unchanged. This slice is
source-reviewed but unverified.
## 2026-08-26 lexer nullable-file authority follow-up

The compiler lexer no longer redeclares `rt_file_read_text`; both read sites
use canonical always-inline `file_read_nullable`, retaining one ABI call and
the same nil/empty lifting. The layer-0 driver source owner remains explicitly
unsafe because importing the runtime facade there would violate layering.
This slice is source-reviewed but unverified.
## 2026-08-26 lexer environment-write authority follow-up

The compiler lexer no longer redeclares `rt_env_set`; all twenty-eight writes
use the canonical now-always-inline `env_set` owner with unchanged boolean ABI
and ignored-result behavior. Array release is the lexer's sole remaining raw
boundary. This slice is source-reviewed but unverified.
## 2026-08-26 lexer array-release provider follow-up

The lexer's final raw boundary remains explicitly unsafe because its `i64`
handle cannot prove ownership. The Rust interpreter provider now rejects a
wrong argument type instead of silently treating it as a successful no-op.
Native C and pure-Simple providers retain registered-handle guards. The valid
Rust path keeps the same single type match and release call. Source-reviewed,
but unverified and unsigned.
## 2026-08-26 transient-promotion boolean-contract follow-up

The Rust interpreter provider for `rt_transient_heap_promote` no longer returns
fabricated `false` for a missing argument; it returns a typed runtime error.
Valid calls still return the provider boolean directly. Four frontend registry
owners remain explicitly unsafe and the ABI stays `i64 -> i8/bool`. This slice
is source-reviewed but unverified and unsigned.
## 2026-08-26 transient-scope arity follow-up

Rust interpreter providers for transient scope begin/pause/end now reject extra
arguments before mutating scope state. Valid zero-argument calls still lift the
provider boolean directly through the registered `() -> i8` ABI. These are
parse-boundary calls, not token-loop calls. Source-reviewed but unverified and
unsigned.
## 2026-08-26 interpreter heap-metric contract follow-up

Six interpreter-only heap metric SFFI handlers now enforce declared arity. The
two by-kind handlers return typed conversion errors for missing/wrong values
instead of fabricated zero; genuine provider zero for out-of-range kinds is
unchanged. Four zero-argument metrics reject extras. These diagnostic calls add
no allocation or provider dispatch on valid paths. Source-reviewed but
unverified, unsigned, and lacking native registry coverage.
## 2026-08-26 memory-attribution contract follow-up

Four Rust interpreter memory-attribution handlers now enforce exact arity and
types. Report/report-print no longer fabricate `n = 16`; set-owner no longer
turns missing/wrong values into a successful no-op; enabled rejects extras.
Valid reporting allocation/sort behavior is unchanged. Native set-owner uses a
separate `(ptr,len)` text ABI, while report functions still lack typed native
registry coverage. Source-reviewed but unverified and unsigned.
## 2026-08-26 memory-profile arity follow-up

Four zero-argument Rust interpreter profiling handlers now reject extra ABI
arguments: harden-check, guard-stats, profile ABI version, and feature bits.
Valid paths retain their genuine results and provider work. None has typed
native registry/header coverage, so interpreter registration is not treated as
cross-lane verification. Source-reviewed but unverified and unsigned.
## 2026-08-26 Unix-socket service contract follow-up

All six service socket declarations are now explicitly `unsafe(ffi)`. Close is
aligned from incorrect `bool` to the native/interpreter `i32` errno contract.
Five server interpreter handlers enforce exact arity/types; recv also rejects a
negative length before allocation. Unknown descriptors, unavailable platforms,
read failures, and invalid UTF-8 now return typed errors rather than fabricated
empty text. Valid UTF-8 conversion reuses the receive buffer instead of making
a lossy owned copy. Native recv remains a pointer/out-length ABI while
Simple/interpreter expose text, so that lane split is explicitly unverified and
unsigned rather than safe.
## 2026-08-26 QMP/client socket provider follow-up

The four client socket interpreter handlers now enforce exact arity/types and
buffer bounds. Write no longer defaults/truncates an invalid length; read-until
no longer defaults stop/max, fabricates empty text for transport failures, or
lossily copies UTF-8. A genuine EOF may still produce empty text. Valid reads
cap initial capacity at `min(max, 256)` and reuse the buffer as `String`,
reducing zero/small-read memory. Source-reviewed but unverified and unsigned.
## 2026-08-26 QMP/SPM raw-call confinement follow-up

The four raw client socket declarations in both QMP and SPM are now tagged
`unsafe(ffi)`. Each module confines them to four non-exported always-inline
owners; all existing connect/write/read/close calls and status checks remain in
the same order and count. No allocation, copy, lookup, retry, or extra dispatch
was added. Native receive lifting remains unverified and unsigned.
## 2026-08-26 interpreter diagram-contract follow-up

Twelve diagram interpreter handlers now enforce declared arity. Method args
and return values accept only their declared text shape; wrong arrays/nil/types
no longer become filtered empty args or ordinary absence. Interpreter string
free validates its one integer handle before the intentional managed-memory
no-op. Valid generation/tracing algorithms and allocations are unchanged.
Source-reviewed but unverified and unsigned; raw Simple declarations and native
pointer-width/lifting remain pending.
## 2026-08-26 diagram raw-declaration follow-up

All twelve seed-standard-library diagram declarations are now tagged
`unsafe(ffi)`, and the ten live call boundaries use explicit lexical unsafe.
Free-string changed from truncating `i32` to pointer-width `i64`. The known
non-NUL Simple text versus native C-string mismatch was not hidden by adding
diagram functions to the unsound C-string lowering table. Call counts and
diagram algorithms are unchanged. Source-reviewed but unverified and unsigned.
## 2026-08-26 span-handle contract follow-up

All six span raw declarations are tagged `unsafe(ffi)` and remain unwrapped
because `i64` cannot prove ownership. The interpreter provider now enforces
exact arity, checked `usize` conversion, ordered ranges, checked handle-ID
growth, and unknown/double-free errors. Valid create/access/free paths retain
one registry insertion/lookup/removal; no extra registry pass or allocation was
added. Follow-up reachability review found no repository consumers, so the six
raw handle functions are no longer exported by either their owner module or the
interpreter FFI aggregate. This reduces the public unsafe surface without
inventing an allocated wrapper for an unused API or changing provider/runtime
work. A static authority contract keeps the private declarations annotated and
prevents raw re-export or new interpreter callsites. Interpreter-only,
source-reviewed, unverified, and unsigned.
## 2026-08-26 SHA-256 handle-contract follow-up

The five interpreter SHA-256 handlers now enforce exact arity. Write requires a
checked explicit length rather than hashing the full payload on malformed input;
handles require `i64`, and allocation rejects counter overflow. All six seed
raw declarations are tagged `unsafe(ffi)` and confined to the six existing
`Sha256Hasher` method boundaries. Free remains explicitly idempotent, matching
existing interpreter/native semantics. Valid hashing complexity and registry
operations are unchanged. The seed integer data carrier versus interpreter
array transport remains unverified and unsigned.
## 2026-08-26 XXH3 legacy-boundary follow-up

All six XXH3 raw declarations are now tagged `unsafe(ffi)` and confined to the
six existing `XxHasher` method boundaries. The Rust provider rejects a `u64`
length that cannot fit `usize` before constructing a slice, removing a 32-bit
truncation hazard without adding another payload pass, registry lookup, lock,
allocation, or copy. The legacy finish ABI still maps an invalid handle to `0`,
which is also a valid digest; this family therefore remains explicitly unsafe,
unverified, and unsigned until a status/out v2 ABI replaces it.
## 2026-08-26 SHA-1 return-contract follow-up

The seed `finish`/`finish_bytes` declarations now match both providers' typed
text/one-argument packed-byte return ABIs instead of exposing packed bits or
passing an ignored output pointer. The native
provider returns a byte-array value rather than binary data mislabeled as text.
The wrapper rejects nil with a stable panic and derives its `u64` from the first
eight digest bytes instead of casting a packed runtime value or fabricating
zero. Interpreter handlers enforce exact arity, explicit checked write length,
and checked handle growth; native pointer length conversion is checked. Valid
hashing retains one payload pass and one registry operation, while scalar
finish reduces the prior hex-format allocation to the required 20-byte result.
Native digest publication uses the packed-array bulk-copy owner rather than
twenty element-dispatch calls.
This remains source-reviewed, unverified, unsigned, and SHA-1 remains unsuitable
for security decisions.
## 2026-08-26 SHA-256 cross-lane return follow-up

SHA-256 `finish` and `finish_bytes` declarations now match provider text and
optional byte-array results. The ignored out-pointer and packed-value-to-`u64`
paths are removed; invalid allocation/finish handles fail closed. The
interpreter now owns a strict registered byte-result handler instead of falling
through generic dynamic dispatch, and native binary output is tagged as a byte
array rather than text. Native write rejects non-platform-sized lengths and
handle allocation rejects counter exhaustion. Scalar finish uses the first
eight digest bytes and native publication uses one packed bulk copy, avoiding
hex formatting and per-element dispatch. Source-reviewed but unverified and
unsigned; signed artifact admission is still absent.
## 2026-08-26 UI WebSocket pure-Simple SHA-1 follow-up

`app.ui.web.ws_handler` no longer declares or calls its four mismatched raw
SHA-1 hooks. Its `write(handle,text)` declaration disagreed with the native
pointer/length ABI and the exact interpreter arity, while write/finish wrappers
fabricated `0`/empty text on failure. The app now calls the canonical
pure-Simple `std.nogc_sync_mut.websocket.handshake.compute_websocket_accept`
owner once per connection handshake. This removes handle ownership, optional
lifting, and foreign binary/text transport from the app boundary. Complexity
remains O(n) over a bounded key-plus-GUID input and no work was added to the
frame send/receive hot path. Wall-clock access now uses the canonical fail-closed
time facade, removing the final raw declaration from this module while retaining
the same provider call and millisecond division. Source-reviewed but unverified;
broader SFFI signing and admission remain absent.

## 2026-08-26 provider-scoped census admission follow-up

The inventory schema now records declaration `provider_id` from `@sffi`
metadata and joins signed admission by `(symbol, canonical source
signature hash, provider_id)`. A matching symbol/signature from another
provider, or a declaration without provider identity, cannot inherit admission.
The census
reports provider-declared rows, provider-missing rows, and symbols naming more
than one provider so attribution debt and provider conflicts remain visible.
Symbol aggregation now calls a symbol fully admitted only when every declaration
row is admitted; mixed admitted/unadmitted declarations are reported as partial
admission and remain migration-required.
It also stops calling `unsafe` tag plus contract metadata “minimized”: that proves
neither lexical call ownership nor call-site count. It reports contract-declared
unsafe rows separately and emits `unsafe_minimization_status=not_measured`
until an authoritative resolved-call graph supplies that evidence. The existing
module-scoped textual callsite count is retained as an explicitly named estimate
and aggregated once per distinct symbol for migration prioritization; it is not
treated as resolution or lexical-minimization proof. This is an
offline source/evidence-tool correction and adds zero runtime work, memory,
lookup, hashing, or dispatch. Existing numerical tables remain the prior static
snapshot and were not rerun under the no-verification instruction.

## 2026-08-26 multiline unsafe-authority lint follow-up

The pure-Simple raw-SFFI lint now recognizes canonical multiline
`@unsafe(... capabilities: [ffi])` annotations on both raw declarations and
minimal helper functions. Its backward annotation walk is capped at 32 lines,
stops at non-annotation source, and therefore adds bounded compile-time work
without changing generated or runtime code. Regression specifications cover
multiline declarations and helpers. Capability parsing now requires the exact
`ffi` list token; `ffi` appearing only in reason text cannot grant authority.
This was source-reviewed only; tests were not executed. At that point the
Rust-seed HIR still erased the capability list from `UnsafeBlock`; the follow-up
below closes that representation gap.

## 2026-08-26 Rust-seed unsafe-capability retention follow-up

Rust-seed parsing now retains the exact capability identifiers on unsafe AST
blocks, HIR lowering preserves them, and the raw-FFI checker grants authority
only when `ffi` is present. Bare unsafe blocks and `raw_ptr`-only scopes no
longer satisfy foreign-call enforcement. MIR continues to erase the metadata,
so generated code and runtime call paths are unchanged. Parser/HIR/checker
regression cases cover retained `ffi`, empty bare blocks, and rejection of
non-FFI scopes. Capability collection is one linear header-token pass with one
small vector per unsafe block; there is no per-call runtime allocation. This
slice was source-reviewed only and deliberately not executed. Raw-call identity
now comes exclusively from HIR's extern set, which includes imported externs and
aliases; `rt_`/`spl_` prefixes alone no longer misclassify pure local functions.
The check remains one existing O(1) set lookup per analyzed global call.
Strict-profile MIR admission skips the HIR walk in O(1) when the semantic extern
set is empty; modules that actually contain or import externs receive one
fail-fast linear pass. Lower profiles remain temporarily permissive during the
large migration and therefore remain classified unsafe/unverified by the
census. Enabling the gate globally before those callsites are tagged would
break ordinary builds, so that sequencing shortcut was explicitly rejected.
Source-reviewed, not executed.

## 2026-08-26 dedicated-host POSIX mmap follow-up

The five raw mmap/file declarations in `dedicated_host_posix.spl` are now
explicitly `unsafe(ffi)` and confined to five always-inline private owners.
Mapped byte lifting validates `0..255` during the existing conversion loop and
returns a typed error instead of narrowing arbitrary integers; preload size is
checked exactly, including empty files. Valid execution retains one foreign
call, one conversion pass, and the pre-existing output allocation/copy. A static
authority contract pins declaration/call confinement and lifting checks.
The interpreter mmap-byte handler now rejects wrong arity and filesystem failure
with typed errors instead of delegating to the legacy `Nil`-returning reader;
success still performs one `fs::read` and directly lifts its sole byte buffer.
File-size lifting now uses checked `u64`-to-`i64` conversion rather than wrapping
oversized metadata into a negative sentinel.
Follow-up provider tracing found both the Rust native export and the
pure-Simple/C-bootstrap byte readers. This corrects the earlier missing-provider
classification, but does not promote the boundary: the Rust exports return
`RuntimeValue::NIL` for invalid paths, read failures, and allocation/lift
failures, while the safe-looking Simple declaration returns only `[i64]`.
The dedicated-host declaration now preserves that provider state as `[u8]?`
and lifts `nil` to `Result.Err` before accepting the owned byte array. A valid
empty file remains `Some([])`, so zero length no longer defeats failure
detection. Matching the provider's byte-array element type also removes the
former O(n) i64-to-u8 conversion, second array allocation, and full payload
copy. A preliminary existence/stat call, a second read, a per-element foreign
loop, and a sentinel byte were rejected because they are racy, slower, or
ambiguous. The raw provider remains explicitly unsafe, unverified, and
unsigned pending signed admission and cross-lane evidence. Source-reviewed
only; checks were not executed.

## 2026-08-26 Base64/Base64url contract follow-up

Interpreter Base64/Base64url handlers now enforce exact arity, explicit bounded
encode length, strict alphabet decoding, and strict UTF-8 lifting instead of
nil/empty or lossy text. The C Base64url oracle returns null for malformed
arguments, invalid alphabet/length, arithmetic overflow, or allocation failure;
its test-only declarations are optional, tagged `unsafe(ffi)`, and lifted once
through fail-closed wrappers. C decode validates while producing output and
frees on rejection; encode/decode remain single-pass with one output allocation
and no preflight alphabet traversal. Pure-Simple decoder leniency remains a
separate characterized defect. Source-reviewed but unverified and unsigned.

## 2026-08-26 font handle/bitmap boundary follow-up

The canonical no-GC font owner now tags all twelve raw font/bitmap declarations
`unsafe(ffi)` and confines their existing calls to nine lexical unsafe regions
inside the established higher-level wrappers. Font generation liveness,
selected-asset validation, digest identity, glyph creation, metrics, and release
behavior are unchanged. The pixel hot path retains exactly one direct provider
call and glyph creation retains exactly one bitmap allocation call; no registry
scan, lookup, allocation, copy, branch, hash, or dispatch was added. A static
authority contract pins declaration/call counts and the pixel/glyph hot-path
shape. Bitmap handles remain copyable integers without generation validation,
so this family is unsafe-minimized rather than promoted: it remains unsigned
and unverified pending a typed non-copying bitmap owner and signed provider
admission. Source-reviewed only; checks were not executed.

## 2026-08-26 gamepad duplicate-boundary removal

`app.io.gamepad_sffi` no longer owns a second 20-declaration copy of the
gamepad boundary and its roughly four hundred lines of duplicated wrapper
logic. It is now an export-only facade over the canonical Pure-Simple no-GC
owner, matching the existing runtime-family facade direction. The canonical
owner retains its 20 annotated raw declarations, 20 provider calls, state
checks, event decoding, rumble behavior, and safe deadzone math. Module export
resolution is compile-time, so polling and input hot paths gain no call,
allocation, lookup, branch, copy, or dispatch. The authority audit now rejects
raw declarations, provider calls, and duplicate wrapper bodies in the app
facade. All 20 provider symbols remain unregistered in both seed registry lanes,
so the family is explicitly unsafe, unavailable, unsigned, and unverified—not
silently safe because duplication was removed. Source-reviewed only; checks
were not executed.

## 2026-08-26 volatile/MMIO duplicate-boundary removal

`app.io.volatile_ops` is now an export-only facade over the canonical
Pure-Simple no-GC owner instead of a second eleven-declaration implementation.
Its three native-required u64 read/write/full-barrier entrypoints moved to that
owner and confine exactly one provider call each inside lexical `unsafe(ffi)`
(`raw_ptr` where applicable). The app facade therefore adds no runtime call,
branch, allocation, lookup, copy, or dispatch, and the host audio/GPU daemon
paths retain their direct native operation shape.

Follow-up provider tracing confirmed all eleven operations in native/Rust lanes
and found interpreter implementations for all three fences that were not
registered. The interpreter registry now publishes those fences, all eleven raw
declarations are explicitly tagged, and every generic/native-required wrapper
performs one confined provider operation. The hardcoded false availability and
eleven zero/no-op fallbacks were removed; `has_runtime_volatiles` is truthful,
and a missing provider now fails during interpreter resolution or native
link/admission. This also removes one runtime availability branch per generic
operation. Raw addresses remain caller-trusted, so the family is
unsafe-minimized rather than memory-safe; providers remain unsigned and
unverified. Source-reviewed only; checks were not executed.

## 2026-08-26 provider-language census correction

The backing census no longer reduces implementation provenance to one
priority-selected language. It records every source language observed for each
symbol, distinguishing C definitions, C++ definitions, header-owned C/C++,
Rust exports, Rust interpreter handlers, system C, external C ABI, freestanding
providers, and unknown linked-native providers. The SFFI contract inventory
uses this multi-language field while retaining its existing backing class and
fail-closed signed-admission join. This is static tooling only and adds no
runtime scan, provider lookup, allocation, copy, hash, or dispatch. Existing
global totals were not regenerated in this no-verification slice; zero symbols
remain safe merely because source implementations were observed, and signed
admission still requires fresh cryptographic evidence. Source-reviewed only;
checks were not executed.

## 2026-08-26 HTTP/WebSocket duplicate-boundary removal

Both app HTTP modules are now export-only facades over the canonical
Pure-Simple no-GC HTTP/WebSocket owner. This removes 52 duplicate raw
declarations and roughly one thousand lines of repeated request, client,
server, WebSocket, URL, and status wrapper code while preserving the complete
public API, including the live LLM Caret `app.io.http_ffi` caller. The canonical
owner additionally rejects negative client/server/WebSocket handles rather than
treating every nonzero integer as valid. Export resolution is compile-time, so
request and WebSocket hot paths retain the same 29 provider calls with no added
allocation, lookup, branch, copy, hash, or dispatch. Both existing HTTP
authority audits now require one 26-declaration owner and two raw-free app
facades. Provider coverage remains incomplete and WebSocket empty/failure
ambiguity remains explicit, so the family is unsafe, unsigned, and unverified.
Source-reviewed only; checks were not executed.

## 2026-08-26 CUDA owner authority and provider closure

The 25-declaration `nogc_sync_mut` CUDA I/O owner now has explicit
`unsafe(ffi)` authority and a machine-readable `contract:` statement on every
raw declaration. Two pointer-write declarations were corrected from a false
`i64` result to the provider's exact unit-returning ABI. The missing native
registry rows for device-to-device copy, extended launch, and error text were
added, and the already-implemented extended-launch interpreter handler is now
registered. All 25 identities are consequently present in both registry
lanes; this is provider closure, not signed admission.

The feature-enabled interpreter launch paths now pass the borrowed function
name span directly to the Rust provider instead of first allocating a
temporary `CString` that the provider immediately copied again. CUDA error
text now comes from static C strings rather than allocating and permanently
leaking one `CString` per call. These changes remove allocation/memory costs;
they add no per-call hashing, lookup, dispatch, or synchronization.

The device-name provider is also changed from leaking one allocation on every
query to a process-lifetime cache keyed by the actual CUDA device handle.
Cache lookup is average O(1), successful names allocate once per device, and
invalid handles return static text without entering the cache. The cache uses
a mutex because device-name queries are control-plane operations; it replaces
the substantially more expensive driver query, UTF-8 conversion, allocation,
and leak on every repeated call. Returned byte allocations remain stable even
if the map relocates its `CString` values, and entries are never removed.

The production-source census moves to 2,789 unsafe-tagged declarations, 4,470
unsafe-tag gaps, and 6,224 contract gaps. The `rt_*` subset has 3,307 unsafe-tag
gaps and 5,035 contract gaps. Signed-admitted declarations remain zero without
exact-artifact admission jobs. Source-reviewed; no build or runtime
verification claim.

## 2026-08-26 simple-core string and Any ABI authority

The bootstrap string and dynamic-Any owners now classify all 39 raw
declarations as `unsafe(ffi)` with explicit contracts (35 string, 4 Any). A
provider comparison found that both owners declared `rt_value_float` as an
integer-bit argument and called it through `spl_f64_to_bits`, while the C
provider, Rust provider, and native registry all require an `f64` argument.
Both declarations and calls now use exact `f64`, removing the conversion and
the integer/floating register-class mismatch.

This is zero-cost declaration authority plus an ABI correction; no lookup,
allocation, copy, branch, lock, or generic dispatch is added. The production
census moves to 2,828 unsafe-tagged declarations, 4,431 unsafe-tag gaps, and
6,185 contract gaps. The `rt_*` subset has 3,287 unsafe-tag gaps and 5,015
contract gaps. These artifacts remain unsigned and unverified.

The four dynamic-Any raw operations are now each confined to one private
mandatory-inline lexical unsafe thunk, and the corrected string-parser float
constructor uses the same pattern. Arithmetic, comparison, and parsing bodies
no longer call those raw symbols directly. Mandatory inlining preserves the
direct scalar call shape; no allocation, branch, lookup, copy, or dispatch is
introduced. The confinement pass now covers all 35 bootstrap string
declarations as well: every raw identity has exactly one executable call,
inside its matching private mandatory-inline thunk. Pointer-bearing thunks
request `raw_ptr`; tagged-scalar thunks request only `ffi`. Semantic string
code contains no direct raw call.

The final `simple_core` pass covers `core_values` (eight declarations) and
`core_enum` (five). Every remaining declaration under
`src/runtime/simple_core` is now unsafe-tagged and every executable raw call is
confined to its matching mandatory-inline thunk. The Simple provider's own
`rt_value_float` definition now accepts `f64`; it performs the required bit
projection once internally, aligning Simple, C, Rust, and native registry
register classes end to end.

Adding that explicit scalar projection dependency increases the production
declaration inventory by one, to 7,260. After tagging the 14 declarations in
this pass, production has 2,842 unsafe-tagged declarations, 4,418 unsafe-tag
gaps, and 6,172 contract gaps. The `rt_*` subset has 3,284 unsafe-tag gaps and
5,012 contract gaps. No hot-path branch, allocation, lookup, copy, lock, or
dispatch is introduced; all thunks are mandatory-inline. Signed admission and
runtime verification remain absent.

## 2026-08-26 package SFFI owner consolidation

Package SFFI had three overlapping standard-library owners. The historical
`sffi/package` and `ffi/package` modules duplicated 38 raw declarations,
including unused Cargo wrappers with incompatible C/Rust signatures and a
`cargo_test_doc(package, text)` call bug. They are now declaration-free
facades over `nogc_sync_mut.package_sffi`. The canonical owner and bootstrap
mirror each retain the same 11 package contracts.

The obsolete `rt_package_free_string` declaration/provider/symbol entry is
removed: package hashes have returned runtime-owned Simple text for some time,
so no valid producer existed for that manual-free operation. Hash failure is
now `text?`; existence and directory provider errors are `bool?`, preserving
absence/failure instead of fabricating empty text or false. Every retained raw
call is confined to a mandatory-inline thunk, and both registries carry every
identity.

This removes 40 production declarations overall (7,260 to 7,220), moves the
unsafe-tagged count to 2,864, and reduces unsafe-tag gaps to 4,356 and contract
gaps to 6,110. The `rt_*` subset falls to 3,222 unsafe-tag gaps and 4,950
contract gaps. No runtime lookup, allocation, copy, branch, lock, or dispatch
is added; optional lifting uses only the existing status result. Signed
admission and semantic verification remain absent.

## 2026-08-26 public RuntimeValue closure completion

The remaining public `value_eq`, `value_print`, and `value_println` wrappers
had native registrations but no interpreter providers and no Simple callers.
They are removed from the canonical runtime owner, compiler minimal facade,
re-exports, and public generator specifications instead of adding a second
dispatch path for unused APIs. The scoped canonical owner is now 11 raw
declarations with 11 both-lane providers and no asymmetric or providerless
entries; the compiler minimal facade is 20/20 both-lane contracts.

Backend-internal print/equality lowering remains owned by the native backend
and is not promoted as a public safe wrapper by this change. Removing dead
surface adds no calls, branches, allocations, copies, lookups, hashes, or
dispatch. The retained SFFI remains unsafe and unsigned: provider parity is
not semantic verification or signed artifact admission. Source-reviewed only;
checks were not executed.

## 2026-08-26 repository-wide source census and Cranelift contracts

The authoritative source-only inventory reports 7,259 production-source
declarations across 3,815 symbols. Of these, 2,764 declarations are explicitly
tagged unsafe and 4,495 still lack an FFI unsafe tag; after the Cranelift
update, 6,249 lack a recognized
return/error contract. The `rt_*` subset contains 5,806 declarations across
3,051 symbols, with 3,332 unsafe-tag gaps and 5,060 contract gaps. No
declaration is cryptographically admitted because no exact-artifact admission
jobs were supplied. These are source inventory facts, not verification claims.

The 78-declaration Cranelift SFFI owner was the largest production owner whose
declarations were all already unsafe-tagged but contract-unclassified. Its
annotations now distinguish the valid empty-string zero representation from
the Cranelift handle/value convention, where zero or false is the failure or
invalid-input sentinel and invalid void operations are ignored. All 78 rows
are consequently machine-classified as unsafe with a declared contract. No
signature, wrapper body, branch, allocation, copy, lookup, lock, or dispatch
changed; this is zero-cost contract metadata. The bridge remains unsafe,
unsigned, and semantically unverified.

## 2026-08-26 providerless no-GC API removal

The no-GC runtime is reference-counted and has no `rt_gc_init`,
`rt_gc_malloc`, or `rt_gc_collect` implementation in C, Rust, or the
interpreter. The similarly named pure-runtime collector is a documented
zero-return placeholder without shared allocator state, so it is not a valid
replacement. The three providerless declarations, wrappers, exports, and
public interning specs were removed instead of fabricating successful GC.

Three MCP loops had periodic collection hooks; one declared the missing symbol
directly and two imported the missing canonical wrapper. They could not collect
anything and would attempt resolution on request 100. Those hooks, counters,
increments, modulo operations, and branches were removed. This does not worsen
actual memory reclamation because no collector existed; it removes per-request
work and a delayed unresolved call. Long-session memory behavior still needs
measurement against the real reference-count owner before adding any policy.

The canonical RuntimeValue owner now has 14 declarations: 11 in both registry
lanes, 3 one-lane, and zero providerless. Compiler-minimal now has 23: 20 both,
3 native-only, and zero missing/interpreter-only. This is closure progress, not
signed admission or semantic verification; all remaining wrappers are unsafe
and unsigned. Source-reviewed only; checks were not executed.

## 2026-08-26 providerless pointer-era value API retirement

Eight more active declarations—raw string creation, type projection, release,
four arithmetic operations, and less-than—had no C, Rust, or interpreter
provider. Apparent consumers were unrelated name collisions plus one obsolete
minimal-FFI sample. They were removed from both active owners, facades/exports,
and the public interning specifications. The sample now exercises only tagged
scalar constructors, predicates, and projections that have both registry
lanes. Full Rust provider-construction fixtures remain internal to the
generator and are not published into the Simple API.

The canonical RuntimeValue owner is reduced from 25 to 17 declarations, with
closure 11 both, 3 one-lane, and only the 3 GC functions providerless. The
compiler-minimal facade is reduced from 34 to 26 declarations, with closure 20
both, 3 native-only, 0 interpreter-only, and the same 3 GC functions
providerless. No live runtime call was adapted, and the supported scalar path
gains no allocation, copy, branch, lookup, hash, dispatch, or layout work.
Remaining APIs are unsafe and unsigned. Source-reviewed only; checks were not
executed.

## 2026-08-26 dead RuntimeValue inspection/clone removal

Five additional providerless families—string/array/dictionary predicates,
raw string projection, and raw clone—had no consumer outside declarations,
facades, exports, and mirrored generator templates. They were removed from all
of those surfaces. The generated string-constructor test retains its live
nonnull construction and release assertions without depending on the removed
inspection APIs.

The canonical RuntimeValue owner is reduced from 30 to 25 raw declarations,
with closure 11 both lanes, 3 one-lane, and 11 providerless. Compiler-minimal
is reduced from 39 to 34 declarations, with closure 20 both, 3 native-only, 0
interpreter-only, and 11 providerless. No executable callsite was removed or
adapted, so there is no runtime call, branch, allocation, copy, lookup, hash,
dispatch, or layout change. Remaining APIs stay unsafe and unsigned.
Source-reviewed only; checks were not executed.

## 2026-08-26 dead RuntimeValue container-constructor removal

The providerless `rt_value_array_new` and `rt_value_dict_new` families had no
consumer: every occurrence was a declaration, direct wrapper, re-export, or
generator template. They were removed from the canonical no-GC owner, its
async facade, the compiler-minimal duplicate, the compiler backend re-export,
and both mirrored generator specifications. This prevents a later generation
pass from recreating the dead raw-pointer API.

The canonical RuntimeValue owner is reduced from 32 to 30 raw declarations,
with closure 11 both lanes, 3 one-lane, and 16 providerless. The compiler
minimal facade is reduced from 41 to 39 declarations, with closure 20 both, 3
native-only, 0 interpreter-only, and 16 providerless. Because no callsite
existed, the removal changes no runtime call, allocation, copy, lookup, branch,
hash, dispatch, or memory layout. Remaining boundaries are still unsafe and
unsigned. Source-reviewed only; checks were not executed.

## 2026-08-26 SQLite duplicate-boundary removal

Both app SQLite modules are now high-level-only facades over the canonical
Pure-Simple no-GC owner. This removes 54 duplicate raw declarations and more
than one thousand lines of repeated connection, statement, query, transaction,
and row-wrapper code. The live `app.io.context_ops` consumer retains its exact
high-level types/functions; raw `rt_sqlite_*` handles are deliberately not
re-exported from either app path. The canonical placeholder builder remains the
single implementation. Export resolution adds no runtime wrapper call, query,
allocation, lookup, copy, or dispatch. Existing SQLite audits now require one
27-declaration/26-call owner and two raw-free facades.

This is unsafe-surface minimization, not SQLite promotion. The legacy contract
still has done/failure and nullable-text ambiguity, zero typed-native registry
coverage, interpreter-only registrations, unsigned providers, and no admitted
artifact evidence. PureDatabase remains the preferred native Simple database.
Source-reviewed only; checks were not executed.

## 2026-08-26 legacy regex duplicate-boundary removal

The app legacy regex module is now an export-only facade over the API-compatible
no-GC async owner, removing eight duplicate raw declarations and roughly 370
lines of repeated helper code. The retained owner uses `push` for flattened
find-all results; the removed app copy repeatedly concatenated arrays, so this
also eliminates a potential O(n²) accumulation path. All eight retained raw
declarations are tagged `unsafe(ffi)` and their nine calls are lexically
confined. Both native and interpreter registries contain every symbol. Export
resolution adds no regex call, allocation, lookup, copy, hash, or dispatch.

The separate no-GC sync `simple_regex_*` API remains distinct because its names
and named-group scanning implementation differ; it was not folded through a
wrapper hop. Regex false/empty results can still conflate no-match with provider
failure, and a feature-gated Rust stub provider exists, so the retained family
remains unsafe, unsigned, and unverified. Source-reviewed only; checks were not
executed.

## 2026-08-26 compiler minimal-runtime unsafe-surface restoration

The compiler's minimal runtime facade again marks all 42 raw declarations and
all 42 smallest-scope wrappers `unsafe(ffi)`, including the newer bounded
no-follow file reader. A later snapshot had restored the pre-annotation source
while leaving its two authority policies in place; this change reconciles the
implementation with those policies without adding intermediary dispatch.
Nullable environment lookup and deep-array release outcomes remain optional
instead of being collapsed to integer zero. Each wrapper still performs one
direct provider operation, so there is no new allocation, copy, lookup, hash,
branch, or per-call registry work. Only 15 symbols have both native-codegen and
interpreter registration; 3 are native-only, 6 interpreter-only, and 18 have
neither. The facade therefore remains explicitly unsafe, unsigned, and
unverified. Source-reviewed only; checks were not executed.

## 2026-08-26 RuntimeValue boolean registry closure

Native codegen now carries exact `[I64] -> [I8]` signatures for
`rt_value_as_bool` and the nil, integer, float, and boolean RuntimeValue
predicates. Their Rust C-ABI exports and interpreter handlers already existed;
the missing registry rows were the only closure gap for this group. The
minimal facade therefore improves from 15 to 20 symbols present in both
registry lanes, leaving 3 native-only, 1 interpreter-only, and 18 in neither.
The canonical 32-symbol RuntimeValue owner improves from 6/8/18 to 11/3/18 for
both/one/neither. This changes compile-time signature metadata only: no call,
branch, conversion, allocation, copy, lookup, hash, or generic dispatch was
added. The functions remain unsafe and unsigned because registration is not
artifact admission or semantic verification. Source-reviewed only; checks were
not executed.

## 2026-08-26 file-delete ABI reconciliation

The unused `file_delete_ptr` declaration/export was removed from the compiler
minimal facade, reducing it to 41 explicitly unsafe declarations and wrappers.
The live self-hosted interpreter call remains, but its C provider now accepts
the same `(pointer, length)` ABI already exported by Rust and expected by text
lowering. Native codegen now records the exact `[I64, I64] -> [I8]` signature,
and the call is tagged and lexically confined. The minimal facade has no
interpreter-only symbols after this removal: coverage is 20 both, 3
native-only, and 18 neither.

Both C runtime implementations use the existing bounded stack path conversion.
`rt_file_remove` now delegates to that owner instead of allocating and freeing
a path buffer on every call, so the correction removes one heap allocation and
copy from its common path rather than adding overhead. Long or malformed paths
fail closed. Registration and source parity do not constitute signed admission
or semantic verification; the boundary remains unsafe and unsigned.
Source-reviewed only; checks were not executed.

## 2026-08-26 network duplicate-boundary consolidation

Two GC network compatibility modules each repeated the same 41 raw TCP, UDP,
HTTP, URL, and utility declarations. They are now compile-time export facades
over the currently authoritative no-GC async module, removing 82 production
declarations and two independent ABI authorities. The no-GC sync copy is
retained until its historical TCP export surface can be migrated without an
API break. Export resolution adds no runtime call, allocation, copy, lookup,
branch, hash, lock, or dispatch.

This does not promote the retained network boundary. Its owner still contains
18 providerless UDP/HTTP/URL declarations whose names are absent from both
runtime registries; those interfaces can still fabricate nil in affected
execution lanes and remain unsafe, unsigned, and unverified. The nineteenth
declaration, `rt_file_write_bytes`, is backed but still lacks signed artifact
admission. The network authority ratchet makes the two GC facades raw-free,
records both remaining declaration owners, and reports the exact providerless
set so consolidation cannot be misreported as safety. Production declarations
fall from 7,220 to 7,138; unsafe-tag gaps fall from 4,356 to 4,274 and contract
gaps from 6,110 to 6,076. Source-reviewed only; checks were not executed.

### Pure-Simple network URL codec follow-up

Both remaining network declaration owners now export their matching
Pure-Simple RFC 3986 percent encoder/decoder instead of declaring four
providerless foreign functions. This preserves the public `url_encode` and
`url_decode` names and removes the silent-nil path without adding a forwarding
wrapper, allocation, lookup, hash, lock, or dispatch. The production inventory
falls to 7,134 declarations, 4,270 unsafe-tag gaps, 6,072 contract gaps, and
zero signed-admitted declarations. Sixteen distinct providerless network
identities remain. Source-reviewed only; checks were not executed.

### Pure-Simple network URL parser follow-up

The three legacy `net.Url.parse` variants now adapt the existing matching
Pure-Simple `http_client.types.parse_url` result instead of calling two
providerless high-level-object extern declarations. The parser fails closed on
malformed absolute URLs, authority spoofing, invalid hosts/ports, and opaque
URLs that the legacy `net.Url` shape cannot represent. It is O(n); conversion
constructs the one public `Url` result and adds no registry lookup, foreign
marshalling, signature check, hash, lock, or transport dispatch.

Production falls to 7,132 declarations, 4,268 unsafe-tag gaps, 6,072 contract
gaps, and zero signed-admitted declarations. Fifteen providerless network
identities remain: fourteen UDP operations and `http_request`. Source-reviewed
only; checks were not executed.

### Canonical UDP contract-closure follow-up

The canonical no-GC sync UDP owner now has eleven explicitly unsafe, lexically
confined scalar-handle contracts, including non-blocking mode. All eleven
identities are present in the runtime-symbol manifest, typed native registry,
and interpreter registry. The C provider now matches the Rust/Simple boolean
ABI, rejects receive sizes outside `0..65535`, returns nil on receive failure,
and returns the declared `(bytes, peer_address)` tuple from `recv_from` instead
of bytes alone. Interpreter receive paths now use packed byte arrays instead of
allocating one generic `Value` per byte.
The C send paths now reject non-packed or oversized payloads while still
issuing the required syscall for a valid zero-length datagram, matching Rust.
Non-positive receive timeouts now consistently clear the timeout in both
providers instead of constructing an invalid negative C `timeval`.
Unavailable Windows C stubs return negative send status or typed nil receive/
address results rather than fabricated successful zero values.

Successful send/receive paths still perform one socket operation. Receive
allocates the one required bounded result buffer; `recv_from` additionally
constructs its required address and tuple. No per-call registry lookup,
signature verification, hashing, retry, extra copy, or generic dispatch is
added. Production rises by one declared, tagged contract to 7,133 declarations
and 2,865 unsafe-tagged declarations; unsafe-tag gaps remain 4,268, contract
gaps remain 6,072, and signed admission remains zero. The older fourteen
providerless `udp_socket_*` identities are not yet removed by this closure.
Source-reviewed only; checks were not executed.

### Legacy UDP providerless-surface removal

The canonical UDP owner now also supplies multicast loop, join, and leave for
IPv4/IPv6 with typed boolean provider contracts. The historical `std.net.udp`
module is a compile-time facade over its typed `Result` API, and both network
SFFI owners have removed all fourteen `udp_socket_*` high-level-object extern
declarations. This removes 28 providerless declarations and prevents a
`UdpSocket` object from crossing the raw ABI.

Each option/membership operation performs one handle lookup and one OS socket
operation. C address parsing is stack-only; no wrapper object, per-call
registry lookup beyond that canonical handle lookup, hash, signature check,
generic dispatch, or payload copy is added. Production now has 7,108
declarations, 2,868 unsafe-tagged declarations,
4,240 unsafe-tag gaps, 6,058 contract gaps, and zero signed-admitted
declarations. `http_request` is the sole remaining providerless identity in
this legacy network family. Source-reviewed only; checks were not executed.

### Provider-language statistics correction

The inventory now emits `SFFI language stats` and `SFFI rt_language stats`
rows. Each language row independently reports total declarations,
unsafe-tagged declarations, freshly signed-admitted declarations, and untouched
declarations. The per-symbol summary also replaces the ambiguous historical
`unsafe_tagged` field (which actually counted symbols with a gap) with
`all_declarations_unsafe_tagged` and `unsafe_tag_incomplete`.

This is reporting hardening only: detected C, Rust, external C ABI, or unknown
provider provenance does not prove null safety, ABI correctness, or artifact
identity. Admission remains zero unless the inventory freshly verifies and
joins signed evidence for the exact provider/symbol/signature identity. The
new report shape was source-reviewed but not executed in this tranche.

### Lossless HTTP v2 contract closure

The last providerless legacy network identity, the high-level-object
`http_request`, is removed from both raw network owners. The canonical owner now
calls a tagged `rt_http_request_v2` boundary implemented by native C and the
Rust interpreter and retained by the native/JIT symbol registries. Its result
preserves status reason, raw response headers, binary body bytes, and a distinct
transport/contract error. HTTP error statuses are not converted to transport
failure, malformed inputs fail before network I/O, request/response headers are
bounded to 1 MiB/1,024 fields, status reason to 8 KiB, and body collection to
64 MiB.

The three identical 648-line HTTP modules are reduced to one canonical
implementation plus two compile-time facades. Redirect work is performed only
when requested by the client and capped by `max_redirects`. Ordinary requests
perform no per-call admission, hash, signature, name lookup, generic dispatch,
or compatibility-wrapper allocation. Native v1 callers do not pay for v2
metadata; v2 performs only the allocations/copies required to return headers,
reason, and body to the public response API.

Estimated source counts are now 7,107 production declarations, 2,869
unsafe-tagged declarations, 4,238 unsafe-tag gaps, 6,056 contract gaps, zero
legacy network providerless identities, and zero signed-admitted declarations.
This tranche is source-reviewed only; builds, lint, tests, and benchmarks were
not executed.

Native C deliberately rejects `https://` with a typed transport error because
its core provider implements plain HTTP only; the Rust interpreter uses its TLS
HTTP provider. HTTPS parity therefore remains open, but neither lane silently
downgrades HTTPS or manufactures a successful response.

### Privileged CPU providerless-boundary removal

ARM32, ARM64, and RV32 CPU owners no longer declare 63 genuinely unbacked
`rt_*` identities. They contain 60 direct target instructions, each confined
to its own `inline_asm` capability block. Three unused ARM32 declarations were
removed; ARM32 MPIDR is now one coherent register read instead of two missing
half-word calls, and ARM64 interrupt masks use exact immediate instructions.

This bounded family now has zero raw SFFI declarations and therefore zero
unsigned provider calls. It has not become generally safe: privileged inline
assembly remains unsafe, source review is not compiler/hardware proof, and no
artifact signature/admission evidence exists. The focused static ratchet was
added but not executed. No branch, allocation, copy, lookup, hash, lock,
signature check, or generic dispatch was added to the per-operation path.
The two checked-in x86 example provider snapshots also drop 114 stale matching
nil/no-op definitions; unrelated architecture helper definitions are retained.

The RV64 follow-up removes another ten CPU declarations and its 91-line
freestanding C switch/provider implementation. Thirty named direct instructions
replace the generic CSR and register bridge. Across the bounded privileged CPU
family, 73 SFFI declarations are removed and 90 operations now carry minimal
`inline_asm` authority. This improves dispatch shape but remains unsigned and
hardware/compiler-unverified.

### Architecture context and timer authority

Nine ARM32/ARM64/RV32 context declarations remain because the assembly ABI
cannot be safely replaced without scheduler ownership redesign. All nine
declarations, calls, and wrapper methods are now explicitly
`unsafe(ffi, raw_ptr)`. Stack alignment is established once on construction,
and RV32 architecture mismatch fails closed. The by-value save-target defect
is recorded and blocks safe/verified promotion.

Thirteen unbacked ARM timer declarations and 22 weak nil/no-op example
definitions are removed. Ten direct capability-confined instructions replace
them; ARM32 uses one coherent MRRC counter read. No per-switch/per-tick
allocation, copy, lookup, hashing, lock, signature check, or generic dispatch
is added. The bounded context family remains unsafe and unsigned; timer
assembly is source-reviewed but hardware/compiler-unverified.

### User-entry and VirtIO input authority

Six ARM32/ARM64 privilege-transfer declarations, four dependent wrappers, and
all raw calls now carry explicit FFI authority. Existing scalar validation and
authenticated reap equality remain unchanged; no safe or signed promotion is
claimed.

Fourteen ARM64/RV64 VirtIO input declarations and four wrappers are explicitly
unsafe because one event is reconstructed from a provider-global snapshot over
six calls and queue corruption aliases ordinary no-event. Non-`1` poll results
no longer produce an event. There is no new per-poll allocation, copy, lookup,
hash, lock, signature check, retry, or provider call. A one-call status/out ABI
remains required for safe typed admission; current artifacts are unsigned and
unverified.

### SBI and ARM32 topology authority

Six raw architecture declarations are newly explicit unsafe boundaries: RV32
SBI remains genuinely providerless; RV64 SBI/CLINT has a direct target C leaf
but no signed artifact admission; and ARM32 topology reads a split boot-global
address from an example-only provider. No declaration in this tranche is
verified-and-signed.

Two RV64 extension probes now preserve their boolean API while requiring both
`error == success` and a nonzero value. The legacy IPI path supplies an actual
stack-word pointer, while CLINT fallback applies `hart_mask_base`, rejects
unrepresentable IDs, and terminates after the highest set bit. The stack word
does not allocate or escape the synchronous ecall. There is no per-call hash,
signature verification, lookup, lock, retry, generic dispatch, or payload copy.

This is source hardening, not whole-module verification. Exact ABI layout,
provider/firmware identity, cross-target compiler behavior, and hardware/QEMU
execution remain missing evidence, so the repository-wide SFFI verdict remains
unsafe/incomplete rather than safe and verified.

#### Provider-aware inventory snapshot (2026-08-26)

The full inventory reported 11,370 `rt_*` declaration rows and 3,035 distinct
`rt_*` symbols. Of the declarations, 2,798 are unsafe-tagged, 8,323 are
untouched, and zero are exact-artifact signed-admitted. Production scope alone
contains 5,667 rows: 2,620 unsafe-tagged, 2,970 untouched, and zero admitted.

Provider provenance is many-to-many. The largest exact combination rows are:

| Observed provider languages | `rt_*` declarations | Unsafe-tagged | Untouched | Signed-admitted |
|---|---:|---:|---:|---:|
| C + Rust export + Rust interpreter | 5,622 | 708 | 4,706 | 0 |
| Rust export + Rust interpreter | 1,385 | 585 | 786 | 0 |
| C + Rust interpreter | 1,226 | 342 | 867 | 0 |
| None observed | 1,165 | 400 | 757 | 0 |
| Rust interpreter only | 702 | 346 | 355 | 0 |
| C + C/C++ header + Rust interpreter | 302 | 29 | 273 | 0 |
| C only | 262 | 58 | 204 | 0 |
| C + C/C++ header + Rust export + Rust interpreter | 250 | 33 | 217 | 0 |
| Rust export only | 187 | 77 | 110 | 0 |
| C++ only | 126 | 126 | 0 | 0 |

These are disjoint combination rows, not independent language totals. A
declaration with both C and Rust providers appears in one combined row. Provider
detection does not prove matching ABI, null safety, ownership, or artifact
identity; only the currently empty signed-admission column represents that
stronger state.

### RISC-V cache-maintenance authority

Eight shared CMO declarations are newly unsafe-tagged and lexically confined.
They remain unsigned: RV64 has direct target C instruction leaves, while RV32
has no matching provider for the imported `rt_riscv64_*` identities. No safe,
verified, or signed promotion is claimed.

The count-only helpers are now O(1) rather than O(cache lines), handle zero
stride without hanging, and saturate instead of wrapping. Production RV32/RV64
loops reject wrapping ranges and retain one direct CMO call per covered line.
No per-line allocation, copy, lookup, lock, hash, signature check, retry, or
generic dispatch was introduced. Whole-repository signed admission remains
zero.

The focused CMO authority/hot-path ratchet passed. Bootstrap-seed type checks
passed for the shared CMO module and both HAL modules; the canonical HalCache
spec executed 18/18 examples with zero failures in 150 ms, including the three
new edge cases. Optimizer analysis found no general-pattern or allocation
opportunities; RV64 stride widening was hoisted once per range after its
loop-invariant finding. These are useful source/interpreter results, not
cross-target assembly, firmware, hardware, RSS, or signed-artifact evidence.

### Canonical bare-metal MMIO authority

Fifteen duplicate MMIO declarations across four noalloc consumers are reduced
to six canonical `unsafe(ffi, raw_ptr)` declarations and six inline wrappers.
The nine-row declaration reduction does not change provider-call count: each
access remains one direct volatile read or write. No allocation, copy, lookup,
lock, hash, signature check, retry, generic dispatch, or compatibility branch
was added.

The native and interpreter providers exist, but arbitrary-address validity,
alignment, ordering, device ownership, ABI parity, and exact signed artifact
identity remain unproved. These six leaves are unsafe-tagged, not safe or
signed-admitted; whole-repository signed admission remains zero.

The Rust interpreter now rejects non-positive, host-width-invalid, and
misaligned addresses before volatile access, eliminating those immediate UB
classes. The valid hosted path adds only scalar checks; error strings allocate
only after rejection. Native bare-metal access remains branch-free and unsafe,
because address zero and mapping policy are target-defined.

The focused Rust MMIO test did not execute: `simple-runtime` currently fails
first with unrelated `E0432` export drift in spin-loop, TLS, and UDP families.
That blocker is recorded separately. The MMIO Rust change therefore has static
ratchet/format evidence only and is not labeled runtime-verified.

### Volatile MMIO owner and semihost UART

Thirteen declarations in the production/freestanding OS MMIO owner and two in
the semihost UART path moved from untagged debt to explicit `unsafe(ffi)` and
`raw_ptr` authority. Thirteen OS raw calls and three semihost calls are now
lexically confined. The eight hot OS read/write wrappers and eight unaliased
entry-closure names are inline, with aliases reusing the owner wrapper; there is
no extra runtime dispatch, allocation, copy, lookup, lock, or admission work.

The hosted interpreter's eight volatile read/write entries now reject null,
negative, host-width-invalid, and misaligned integer addresses before entering
Rust unsafe code. The target C and Rust ABI leaves remain raw and cannot prove
device mapping, ownership, ordering, or lifetime. These changes therefore
reduce unsafe scope and immediate hosted UB, but do not make arbitrary-address
MMIO safe.

The focused authority ratchet and both bootstrap-seed Simple checks passed.
Optimizer O3 reported only MIR opportunities and zero general/allocation
patterns. The existing semihost transport spec passed 23/23 in 36 ms with no
skip/drop, although it covers transport policy rather than physical UART MMIO.
Rust execution is still blocked by `simple-runtime` export drift;
whole-file formatting is also blocked by older unrelated drift in the shared
provider file. Exact signed-artifact admission remains zero, so this tranche is
unsafe-tagged and statically checked, not verified or signed.

The refreshed repository-wide ratchet reports 11,356 `rt_` declarations:
2,826 unsafe-tagged, 8,281 untouched, and 0 signed-admitted. Across every SFFI
name it reports 13,011 declarations, 3,145 tagged, 9,461 untouched, and zero
signed-admitted. The ratchet itself is not green because its checked-in baseline
has 540 newly untagged and 3,435 stale entries after concurrent tree changes.
The independent null/signature guard also fails on multiple existing families,
including fabricated-zero dynload/symbol lookup, boolean/integer ABI coercion,
TCP/UDP contracts, and missing checked crypto declarations. These failures are
authoritative evidence that whole-SFFI safety and verification are incomplete.

### Checked dynload, symbol lookup, and boolean transport

The fabricated-zero dynload/symbol findings and boolean-to-integer coercion are
now removed from the global guard. Status/out providers are present across both
C owners, the Rust runtime, interpreter, dispatch table, and codegen registry;
outputs are initialized before failure. The exact Linux snapshot sabotage
passes after proving write seals and pathname-replacement resistance.

Typed `bool()` and `bool(i64)` calls now use direct status/out thunks, not the
integer dispatcher. Their hot path has no allocation, copy, lookup, lock, or
generic array dispatch. The C cross-lane harness passes 10/10 cases. The Rust
tests did not execute because the existing spin-loop/TLS/UDP export drift still
stops `simple-runtime` compilation before the target.

The global null/signature guard remains red for independent TCP/UDP, crypto,
and other runtime contract drift. Signed admission is still zero. The checked
integer call API also retains an existing per-call two-element array allocation;
that performance debt is not introduced by the typed boolean thunks and remains
open for a scalar status/out migration.

### TCP/UDP scalar ABI and timeout closure (2026-08-26)

The fresh inventory reports 13,009 SFFI declarations and 11,352 `rt_`
declarations.  The `rt_` rows contain 2,826 unsafe-tagged, 8,277 untouched, and
zero signed-admitted declarations.  Of 3,033 distinct `rt_` symbols, 1,433 are
fully unsafe-tagged, 1,600 remain incomplete, 1,046 are untouched, and none are
admitted.  Therefore all-SFFI safety and signing remain false.

The AOT C TCP status ABI now matches Rust, Simple, and Cranelift: boolean
parameters/returns are `bool`/I8 rather than integer truthiness.  The complete
TCP declaration family is registered for native codegen.  UDP C declarations
use the same semantic bool ABI.  Invalid family tags fail rather than selecting
IPv4.  C connect timeout no longer discards its budget; it uses nonblocking
connect, `poll(POLLOUT)`, `SO_ERROR`, and restores flags before returning a
descriptor.  Unsupported-platform reads/addresses return nil and writes return
`-1`, preserving empty EOF/datagram values separately from failure.

The focused C syntax check passed with one unrelated comment warning.  TCP
consumer, UDP, and network authority audits passed.  The global null/signature
guard now reports only two missing checked ECDSA facade declarations and one
raw SSH RSA/Ed25519 import; it remains FAIL and correctly blocks a global claim.
The Simple environment-owner check passed using the bootstrap seed with its
honest warning.  O3 optimizer analysis found ten generic low-confidence MIR
bounds-check opportunities and no general allocation/copy opportunity.

Optimized before/after object evidence: `rt_io_tcp_close` 18 -> 13 bytes,
`set_nonblocking` 85 -> 79, `set_nodelay` 51 -> 38, UDP connect 211 -> 211,
UDP close 13 -> 13.  TCP read is 351 -> 395 bytes because it validates negative
sizes/allocation state and releases on provider failure.  Both versions retain
one array creation on the successful path; the new call is failure-only free.
No dynamic lookup or heap allocation was added to scalar hot leaves.

The whole C guard remains FAIL for pre-existing `F_ADD_SEALS`/`F_SEAL_*`
feature-macro drift and an unrelated `runtime_process.c` call-arity defect.
Rust focused tests remain blocked earlier by the recorded runtime export drift.
This tranche is source/syntax/contract checked and unsafe-minimized, but not a
verified signed provider admission.

### Checked ECDSA and SSH facade ownership closure (2026-08-26)

The common ECDSA P-256 module already used canonical typed checked wrappers;
the global checker incorrectly demanded duplicate raw extern declarations.
The checker now enforces the correct architecture: raw checked declarations in
`signature_sffi`, exact safe-wrapper imports in common crypto, and no raw
checked or legacy ECDSA extern in the common facade.  An unused raw RSA verifier
declaration was removed from the SSH session.  No runtime operation was added.

The global null/signature guard now passes.  The SSH module source check passes,
and optimizer analysis reports only pre-existing opportunities in the large
session body.  The post-change census is 13,007 total SFFI declarations and
11,350 `rt_` declarations, with 2,825 unsafe-tagged, 8,276 untouched, and zero
signed-admitted `rt_` rows.  There are 3,032 distinct `rt_` symbols: 1,433 fully
tagged, 1,599 incompletely tagged, 1,045 untouched, and zero admitted.

This is a static contract/tooling PASS, not universal safety.  The inventory
proves that 1,599 `rt_` symbols still have incomplete declaration tagging and
that no exact provider artifact has passed cryptographic admission.  The next
work must continue census-led unsafe minimization and produce real admission
jobs rather than treating the green source guard as a signature.

### Providerless async ABI removal (2026-08-26)

The unused `nogc_async_mut.async.sffi` module contributed 19 generic foreign
declarations despite having no provider and no imports.  The native linker also
permitted three corresponding zero-return stubs.  Both the module and those
permissions are removed; the canonical Future, Promise, and AsyncIO owners stay
pure Simple.

The new authority audit passes, all three owner checks pass, and the async
basics interpreter spec passes 25/25.  The change removes runtime fallback
surface and adds no hot-path work or allocation.  The total SFFI declaration
count therefore drops by 19; `rt_` counts and signed-admitted counts are
unchanged, including zero signed-admitted providers.

### Generic interpreter all-integer dispatcher removed (2026-08-26)

The current backing-aware census classified all five `call_ffi_0..4`
trampolines as genuinely missing.  The containing module contributed 14 SFFI
declaration rows and was referenced only by private, unused bridge helpers.
That module, those helpers, and the unused package exports are now removed.

The authority guard passes and preserves the typed native registry.  The
initializer source check passes.  The surviving bridge cannot yet be directly
checked because its unchanged Rust-like import/struct syntax produces 24 parser
errors; a focused bug records that blocker.  Optimizer analysis found 19
low-confidence MIR opportunities and no general allocation/copy pattern.
Lint was attempted once but produced no verdict because the deployed compiler
cannot resolve `Linter.lint_source_for_parsed_append`; the existing stale-
snapshot lint-subsystem bug remains the authoritative blocker.

The change removes O(arguments) array construction, signature erasure, and
generic indirect dispatch from the only possible path; it adds no instruction,
allocation, lookup, or copy to the retained native registry.  Total SFFI rows
drop by another 14 to an expected 12,974, while the 11,350 `rt_` rows and zero
signed-admitted rows are unchanged.  This remains unsafe-surface reduction,
not universal verification.

### Providerless QUIC ABI removed (2026-08-26)

The native-quiche layer had no provider and was permanently gated unavailable,
but retained 14 production and 28 mirrored-test `rt_quic_*` declarations.  All
42 declarations are removed.  The public connection surface now executes only
its existing pure-Simple terminal-state behavior, and the authority audit
prevents raw QUIC declarations or the deleted `quic_sffi` owner from returning.

The connection source check passes, the compatibility spec passes 12/12, and
optimizer analysis reports no opportunity.  All leaves remain O(1); no
allocation, copy, lookup, or dispatch was added.  The current repository census
is 12,929 SFFI rows, 11,305 `rt_` rows, 3,018 distinct `rt_` symbols, 1,585
symbols with incomplete unsafe tagging, 1,031 untouched symbols, and zero
signed-admitted rows or symbols.  Native QUIC remains unavailable rather than
being mislabeled safe or verified.

### Dead executable-memory generator ABI removed (2026-08-26)

Sixteen proposed `rt_*exec_memory*`, protection, and generic function-pointer
declarations had no implementation or consumer outside their specification.
The spec is deleted rather than marked unsafe or allowed to generate an RWX
parallel loader path.  The authority audit passes and retains the real
`smf_mmap_native` W^X owner (`PROT_READ | PROT_EXEC`).

No executable code changed, so runtime time and memory behavior are identical.
The current census is 12,910 total SFFI rows, 11,286 `rt_` rows, 3,000 distinct
`rt_` symbols, 1,567 with incomplete unsafe tagging, 1,013 untouched, and zero
signed-admitted.  This tranche removes exactly 16 declaration rows; three other
rows moved in concurrent upstream changes incorporated by the rebase.

The mandatory push gate caught stale interpreter-gap rows for the removed ABI.
All four relevant ledgers were narrowed by exactly those 16 entries.  The
focused interpreter-gap scan now passes (238 checked, zero new/stale).  The
repository's broader seed, unbacked, and raw-unsafe ratchets still report
unrelated concurrent drift and are not claimed green by this checkpoint.

### Live executable-memory W^X provider enforcement (2026-08-26)

The loader's RW-to-RX policy is now enforced by the Unix, Windows, core-C
bootstrap, and Rust interpreter providers rather than trusted only from Simple
callers. All reject a WRITE+EXEC mask before the OS call; Windows no longer
contains a `PAGE_EXECUTE_READWRITE` mapping or protection route. Invalid
legacy unmap extents also fail before conversion to an unsigned platform size.

The strengthened provider audit passes in 0.07 seconds with 2,560 KiB peak RSS.
Successful normal operations keep the same syscall count and add no allocation,
copy, lookup, or dispatch. Declaration counts are unchanged: 12,910 total,
11,286 `rt_`, 3,000 distinct `rt_`, 1,567 incompletely tagged, 1,013 untouched,
and zero signed-admitted. This is W^X contract enforcement, not evidence that
the live provider or whole SFFI surface is signed or universally verified;
hosted non-coherent instruction-cache synchronization remains open.

Unix and GNU core-C syntax checks pass. The Rust sabotage test is present but
its crate currently fails earlier on unrelated missing compiler exports and
lowerer fields, so no Rust test PASS is claimed.

The cache-coherence follow-up moves synchronization into the existing RX
provider transition. Unix native/core-C providers use the compiler cache-clear
primitive on non-x86; Windows uses `FlushInstructionCache` and restores the old
protection on failure. The Rust interpreter rejects non-x86 executable
transitions before changing protection because that lane has no verified host
primitive. On x86-64 the helper path is compiled away: assembly retains one
`mprotect` call and the W^X mask test, with no added allocation, lookup, copy,
or dispatch. The repeated audit remains 0.07 seconds / 2,560 KiB peak RSS.
Counts and signed-admission status remain unchanged.

### Signed-admission receipt pipeline repair (2026-08-26)

The shell verifier formerly emitted no `provider_id`, although both inventory
consumers required one and the Simple parser required a framed v1 receipt. A
cryptographically valid job therefore could not join any declaration. The
verifier now emits canonical `simple.sffi-admission.v1`, and the contract test
proves the full provider/source-signature join reaches `reverified` while all
seven existing sabotage cases remain rejected.

The expanded ephemeral fixture passes in 1.5 seconds. This is one-time
admission/census work and adds zero per-call instructions or memory. The test
key is intentionally not a production trust root, so declaration statistics
remain 12,910 total, 11,286 `rt_`, and zero production signed-admitted rows.

### Providerless debug command-output removal (2026-08-26)

Four production modules declared `rt_command_output(cmd) -> text`, but the
backing census found no provider. The text-only shape also erased command exit
status and stderr. All four declarations are removed and their ten scoped call
sites now share one bounded pure-Simple owner over the existing typed
`process_run_bounded` facade. Nonzero exit is `Err`; successful empty stdout
remains distinguishable as `Ok("")`. External values cross as argv or as
positional parameters to a fixed shell script, preventing shell interpolation.

The helper uses one subprocess, O(output) capture, a 120-second timeout, and a
1 MiB cap. It adds no lookup, retry, second process, per-byte loop, generic
dispatch, or unbounded allocation. The compatibility spec passes 3/3 in 6.84
seconds with 176,820 KiB peak RSS under the available Rust bootstrap runner,
including a literal shell-substitution sabotage argument;
five source checks, the authority guard, direct-runtime guard, and optimizer
analysis pass. Lint remains blocked before file analysis by the existing
`Linter.lint_source_for_parsed_append` dispatch defect, so this row is not
reported lint-verified or Stage-4 verified.

The post-change source census is 12,888 total SFFI declarations, 11,264 `rt_`
declarations, 2,986 distinct `rt_` symbols, 1,553 incompletely unsafe-tagged
symbols, 1,002 untouched `rt_` symbols, and zero signed-admitted rows or
symbols. The tranche removes four rows and one distinct providerless symbol;
the retained process provider and wider estate remain unsigned and unverified.

### Interpreter debug-hook gap classification (2026-08-26)

`rt_hook_*` has 42 production declaration rows for 14 distinct symbols in the
sync DAP, async DAP, and generator surfaces. No provider is observed. The
focused source census now reports 42 unsafe-tagged rows, 14 fully tagged
symbols, zero incomplete symbols, and zero signed-admitted rows. The interpreter
classifies an unresolved hook as a typed capability gap; the Rust unit suite
passes 3/3. This remains unsafe and unverified: no provider, artifact signature,
or null/ownership validation exists, and the installed compatibility runner is
too old to count as runtime evidence for this new dispatch.

### Owned SimpleOS C-provider census correction (2026-08-26)

The backing census now scans owned C/C++ source under both `src/runtime` and
`src/os`, still excluding vendor trees. It changes 68 false-missing identities
to `c_runtime_source_only`, including `rt_mem_read_u8`, `rt_pci_get_field`, and
`rt_net_init`; 60 corresponding stale baseline entries were removed. This is
source provenance only—not deployed-binary evidence, ABI/null/ownership
verification, or signature admission. It changes no compiled or hot runtime
path. The current global unbacked ratchet remains intentionally red because it
reports 46 new and 370 stale entries outside this focused correction.

### HDA PCI raw-boundary classification (2026-08-26)

The HDA binding now has four explicitly unsafe raw declarations and four
`@always_inline` lexical owners; the authority audit passes. The change adds no
loop, allocation, copy, lookup, or dynamic dispatch to the audio boot path.
It is not a provider or ABI verification: two symbols have only test-stub
definitions, and existing target providers disagree on field interpretation.
The native-stub spec is blocked before examples by the bootstrap runner's
unregistered `rt_hda_pci_probe_set_mode`, so no runtime PASS is claimed.

### Debug ptrace/DWARF declaration consolidation (2026-08-26)

Four debug consumers now import the canonical `std.sffi.debug` owner instead
of redeclaring ptrace/DWARF externs, removing 46 duplicate raw declaration
rows. The owner audit passes and all four files pass source checking. This
changes no hot-call instructions or memory behavior. It does not verify the
ptrace/DWARF ABI or provider: raw container/string ownership and signed
admission remain absent.

### Providerless legacy CUDA-session removal (2026-08-26)

The no-GC engine2d legacy CUDA session no longer declares or calls its nine
providerless/conflicting CUDA ABI functions. It retains only the allocation-free
four-slot cache/rejection bookkeeping, covered by the same 2/2 spec before and
after the change; source check and the providerless guard pass. No hot-path
work was added. This removes a false CUDA execution surface, not the need for
signed and typed contracts on active CUDA providers.

### Serial raw-owner consolidation and inventory stdout repair (2026-08-26)

The serial family previously had three raw declaration owners, with app and
bare-metal signatures that narrowed arguments relative to the canonical `i64`
ABI and included unadmitted configuration/availability symbols.  The unused
app owner is removed.  The seven canonical no-GC raw declarations are now
explicitly `unsafe(ffi)`; dedicated hardware calls the checked `SerialPort`
façade rather than raw serial functions.  Its unavailable availability query
fails closed as `Err` without a provider call.  The authority audit and source
checks pass, while the no-hardware unit spec covers that error path.

The SFFI inventory's default stdout path now spools the ledger to its private
temporary file before its aggregation passes.  This fixes the concrete
`/dev/stdout` self-read hang and preserves output/schema semantics.  A fresh
source-only census reports 12,816 SFFI rows, 11,192 `rt_*` rows, 1,514
incompletely unsafe-tagged `rt_*` symbols, and zero signed-admitted symbols.
The source-only mode deliberately has no observed provider-language evidence;
the serial provider remains unsafe, unsigned, and unverified.

### Providerless legacy WebGPU-session removal (2026-08-26)

Eleven providerless `rt_wgpu_*` declarations in the no-import legacy
`WebGpuSession` are removed, retaining only its fixed four-slot shader cache
and rejection accounting. The unused parallel `webgpu_ffi` raw owner is also
deleted. The remaining active `webgpu_sffi` owner has eleven explicit unsafe
declarations; its rendering call shape is unchanged. The pure cache spec passes
2/2, source checks and owner guard pass, and optimizer analysis reports only
existing low-level opportunities. The current source-only census is 12,794
SFFI rows and 11,170 `rt_*` rows, with zero signed-admitted declarations.
Active WebGPU remains unsafe, unsigned, and unverified.

### Providerless legacy Metal-session removal (2026-08-26)

The no-GC `MetalComputeSession` had ten raw `rt_engine2d_metal_session_*`
declarations without an owned C/C++/Rust provider or production import.  They
are removed, leaving only the fixed four-slot pure pipeline cache and its
rejection accounting; the separate active GC Metal backend is deliberately
untouched.  The cache spec passes 2/2, source check and providerless guard
pass, and optimizer output contains only existing local dead-code observations.
No loop, allocation, copy, lookup, or dispatch is added to the retained cache
path.  This is boundary removal, not ABI/null/ownership verification or signed
admission of the active Metal provider.

The post-change source-only census is 12,784 SFFI declaration rows and 11,160
`rt_*` rows; it reports zero signed-admitted rows or symbols.  The removed
legacy façade lowers the raw declaration count, but 8,034 `rt_*` declaration
rows remain untouched and the broader estate is not safe or verified.

### Intel Engine2D raw-owner consolidation (2026-08-26)

The GC Engine2D kernel helper no longer owns eleven duplicate raw
`rt_intel_engine2d_*` declarations; it imports the matching no-GC owner
wrappers while retaining the same helper names and one-call operation shape.
Both remaining Intel owners now explicitly tag all 21 raw declarations as
`unsafe(ffi)`, and the authority audit confirms 42 tagged rows with none in
the active backend. The focused uninitialized text-fallback spec passes 2/2;
source checks pass, and optimizer analysis reports no general-pattern finding.

The post-change source-only census is 12,773 SFFI declaration rows and 11,149
`rt_*` rows, with 3,241/2,920 explicitly unsafe-tagged respectively and zero
signed-admitted declarations. This is declaration containment, not an ABI,
ownership, nullability, performance-on-device, or cryptographic verification.

### OpenCL raw-owner classification (2026-08-26)

All 20 declarations in the sole `sffi_opencl` raw owner now explicitly carry
`unsafe(ffi)`. The authority audit confirms that no other Simple library or app
file declares an `rt_opencl_*` ABI. The existing fail-closed OpenCL spec passes
8/8, source check passes, and optimizer analysis reports no general-pattern
finding. No OpenCL dispatch or render-path behavior changes.

The source-only census remains 12,773 SFFI rows / 11,149 `rt_*` rows, now with
3,261 / 2,940 explicitly unsafe-tagged declarations and zero signed admission.
Owned C source is not treated as an admitted artifact, so OpenCL remains unsafe
and unverified.

### ROCm Engine2D raw-boundary classification (2026-08-26)

The two active legacy ROCm Engine2D dispatch owners retain their public
behavior, but all 25 raw declarations are now explicit `unsafe(ffi)`; pointer/
array crossings also declare `raw_ptr`. The authority audit verifies the 12/13
owner split. The existing ROCm spec passes 13/13, including fail-closed legacy
kernel calls; source checks and optimizer analysis report no general-pattern
finding. No GPU call-path instruction, allocation, copy, lookup, or dispatch
is added.

The source-only census remains 12,773 SFFI rows / 11,149 `rt_*` rows, with
3,286 / 2,965 explicitly unsafe-tagged declarations and zero signed admission.
ROCm's C source is not equivalent to ABI/null/ownership verification or an
admitted artifact.

### 3D GPU raw-owner deduplication (2026-08-26)

The four duplicate no-GC `ffi_{cuda,rocm,intel,vulkan}3d` modules are now
compatibility re-exports of their canonical `sffi_*3d` owners. This removes
twelve duplicate raw declarations and duplicate class implementations without
changing public module paths or any GPU call path. The remaining twelve raw
declarations are explicit `unsafe(ffi)`; the authority guard and eight-file
source check pass. Optimizer analysis reports no general-pattern finding for
the four canonical owners.

The source-only census is 12,761 SFFI rows / 11,137 `rt_*` rows, with
3,298 / 2,977 explicitly unsafe-tagged declarations and zero signed admission.
This reduces unsafe surface duplication; it does not verify an ABI/provider or
authorize critical use.

### OpenGL raw-boundary classification (2026-08-26)

The sole active OpenGL raw owner now has nineteen explicit `unsafe(ffi)`
declarations and lexical unsafe calls. Its nullable provider-error text is
represented as `text?`; all public drawing-operation booleans retain their
existing boolean semantics. The owner audit, four-module source check, and
two-case fallback spec pass. Optimizer analysis reports 42 low-level
bounds-check opportunities but no general-pattern finding; this tranche adds
no loop, allocation, copy, lookup, retry, or dispatch to the rendering path.

The OpenGL provider remains unsigned and unverified. This classification does
not establish typed buffer extent, handle ownership, ABI conformance, artifact
identity, or cryptographic admission.

### File-operations raw-boundary classification (2026-08-26)

The common no-GC file owner has nineteen explicit `unsafe(ffi)` raw
declarations, with `raw_ptr` limited to mmap address/extent calls. Its direct
foreign calls are lexical-unsafe and public file-operation APIs retain their
existing operation shape. Optimizer analysis reports 51 low-level bounds-check
and one dead-code opportunity but no general-pattern finding; this tranche adds
no loop, allocation, copy, lookup, retry, or dispatch.

The source check and new raw-boundary guard pass. The bootstrap artifact chosen
by the test predates source registration of
`rt_file_read_regular_no_follow_bounded`, and the legacy lock-resource spec
imports a missing `FileLock` surface; both failures are recorded under
`doc/08_tracking/bug/` and are not accepted as a pass. The provider remains
unsafe, unsigned, and unverified, and legacy non-null mmap/hash text contracts
remain migration work.
