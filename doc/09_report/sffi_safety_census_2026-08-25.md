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
