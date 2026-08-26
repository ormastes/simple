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
