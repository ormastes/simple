# SFFI Safety Census — 2026-08-25

**Revision:** `d813ea19dd9` plus the current linear `origin/main` rebase  
**Command:** `sh scripts/audit/rt-safety-census.shs ...`  
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
| Total | 11,590 | 3,137 |
| Explicitly `@unsafe(... ffi ...)` | 2,826 | 1,779 |
| Contract documented | 1,032 | 391 |
| Cryptographically verified and signed | 0 | 0 |
| Untouched: no unsafe tag, contract, or evidence | 8,515 | 1,825 |
| Unsafe but minimized to a narrow owner | 783 | not yet aggregated |
| Unsafe and not minimized | 10,807 | not yet aggregated |
| Symbols with multiple source-signature hashes | — | 263 |

All 11,590 declaration rows remain fail-closed unsafe in the census. An unsafe
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
| Simple | 687 | 646 | 65 |
| C++ | 219 | 219 | 1 |

These tables answer different questions. Provider provenance is conservative
per declared symbol; the definition scan counts every owned implementation and
therefore includes mirrors and alternative providers.

## Highest remaining debt

Production contains 5,415 declaration rows, of which 2,871 are untouched. The
largest untouched families are `rt_file` (2,529 rows), `rt_process` (966),
`rt_env` (388), `rt_time` (335), and `rt_dir` (217). Test declarations account
for another 5,154 untouched rows and must not be allowed to inflate production
confidence.

The 263 multi-signature-hash symbols are the first ABI-integrity triage set.
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

All SFFI is **not** safe and verified. Current exact status is zero
verified-and-signed symbols, 1,825 untouched distinct symbols, and 263 symbols
whose declarations have multiple source-signature hashes requiring resolved-
type triage. The remaining declarations must stay unsafe until exact provider
evidence and executable contracts prove a narrow safe wrapper.

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
