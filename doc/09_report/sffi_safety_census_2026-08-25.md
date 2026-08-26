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
| Unsafe but minimized to a narrow owner | 797 | 380 |
| Unsafe and not minimized | 10,775 | measured by updated tool |
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
