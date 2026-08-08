# Plan — Global SHA/CAS Interpreter Cache (Option C, strict mode = A)

**Date:** 2026-07-24
**Baseline:** `main` @ `11a84de4150af18c2bd4b5760e5ace705f4b68bd`
**Architecture:** Option **C** default (hybrid stamp index + SHA-256 CAS + dependency-aware
action keys); Option **A** (rehash-everything) is C's strict verification mode. See audit:
`doc/01_research/compiler/cache/global_content_addressed_cache_audit_2026-07-24.md`.

Modes: `C` = default (stamp-fast, SHA-backed identity). `A`/strict = rehash every input on
every lookup — used by CI, release, bootstrap, cache-verification (`--cache-strict`). `B`
= opt-in unsafe local turbo (`--cache-turbo`), never for release/shared trust.

**Status (2026-07-24):** Formal verification LANDED — `src/verification/cache_identity/`
(Lean 4.30.0, 14 theorems, no `sorry`): injectivity core `encode_eq_iff_canon`, 6
field-completeness contrapositives, `no_false_hit`, `stamp_fast_eq_strict` (C≡A bridge),
order-independence. CI gate: `scripts/check/check-cache-identity-formal-proofs.shs` (build
+ trust-bypass scan + theorem presence + gate self-test). Phase-1 implementation (identity
layer, compute-and-log only): `src/compiler/80.driver/cache/action_key.spl`,
`file_stamp.spl`, `cas_store.spl` + specs under `test/01_unit/compiler/cache/`; P1 hole
fixes in `load_session_cache.spl` + `compile_options_hash.spl`. Implementations mirror the
Lean `Model.lean` — divergence between them breaks the proof-to-code correspondence and
must be treated as a defect.

---

## Part 1 — Global SHA/CAS interpreter-cache implementation

### 1.1 Four distinct identities (never one vague "module hash")

- **ContentDigest** = `SHA256(file_bytes)`.
- **InterfaceDigest** — downstream-visible semantics only: exported symbols, types/calling
  conventions, public layouts + accessor/field-wrapper semantics, effects/caps, exported
  macro defs/contracts, exported aspect decls + applicable join-point surface, constants
  used in compile-time eval.
- **ActionDigest** = `SHA256(domain="simple/interpreter-module/v1",
  compiler_executable_digest, live_interpreted_compiler_source_digest,
  frontend_and_cache_schema_versions, target_triple, host_interpreter_arch,
  cfg_and_feature_set, stdlib_variant_and_runtime_family, source_content_digest,
  resolution_witness_digest, sorted_dependency_interface_digests, macro_dependency_root,
  AOP_selection_digest, declared_compile_time_environment_inputs)`.
- **RuntimeGeneration** — session-local identity for mutable globals, loaded symbol
  bindings, JIT addresses, runtime AOP registry, hot-reload gen, active exec/lifecycle refs.

**Encoding rules (all digests):** domain separation, length-prefixing, canonical binary
encoding, explicit versioning, sorted maps/sets. Never concatenate unordered dict iteration
into a text string.

### 1.2 Two global tiers

**Process-global immutable cache** (concurrent, bounded):
```
ContentDigest      -> Arc<SourceBlob>
ParseActionDigest  -> Arc<ParsedModule>
MacroActionDigest  -> Arc<MacroTemplate>
FrontendActionDigest -> Arc<HIR/MIR artifact>
ArtifactDigest     -> Arc<StrictlyParsedSmf>
```
Single-flight construction per key; immutable `Arc` values; bounded memory (LRU / TinyLFU
admission); weak refs for large mmaps; negative results short-TTL only (never permanent).

**Cross-process disk CAS:**
```
$SIMPLE_CACHE/cas/sha256/ab/cdef...     # immutable bytes
$SIMPLE_CACHE/actions/sha256/12/3456... # canonical result manifest -> CAS IDs
```
Writes: private temp file → hash-while-writing (or verify after) → flush → atomic rename
into digest path → treat a lost race with identical bytes as success. Verify bytes match
the requested digest on every disk/remote read. Remote shared cache: trusted-writers or
read-only client policy (content hashing stops corruption, not a poisoned action-key
mapping whose own content digest is internally valid — Bazel remote-cache guidance).

### 1.3 Interpreter realization (global hit → module plan, not reused runtime env)

Per session: (1) fetch immutable parsed/lowered artifact by ActionDigest; (2) allocate new
module runtime instance; (3) fresh mutable globals; (4) fresh function-ownership/overload
state; (5) resolve runtime imports against session; (6) build runtime AOP bindings;
(7) execute top-level init per language semantics; (8) store realized instance only in the
session-local module cache. Gains parse/lower reuse without leaking state between tests.

### 1.4 SMF manifest (every globally-cacheable SMF)

Carries: format/schema version, artifact SHA-256, producing ActionDigest, source SHA-256,
compiler-executable identity, live compiler-source identity, target/backend/options,
runtime family + allowed families, sorted dependency interface digests, macro dependency
root, AOP selection/interface digest, export/interface digest.

Load: (1) path is alias only; (2) resolve → expected `ArtifactId`; (3) strict-parse magic/
version/section-bounds/target/manifest; (4) compare expected ActionDigest; (5) mmap
immutable CAS file; (6) register session-local loaded-module generation. Same path + same
`ArtifactId` → reuse loaded gen; different `ArtifactId` → stale → reload or explicit
reload-required. Old/zero-hash/manifest-less SMFs = local compat input only, never served
from trusted global cache; trigger regeneration when source available. `.lsm`: address
archive by archive SHA, each embedded module by its own blob SHA; in-memory reader, else
digest-qualified private temp (not module-name-only).

### 1.5 Import cycles

Don't recursively hash deps forever. Compute SCCs; hash each as a sorted bundle:
`SCCDigest = SHA256(sorted(member_stable_id, member_source/interface_seed),
sorted(edges_leaving_SCC))`. Members refer to the common SCC identity.

### 1.6 Diagnostics — `simple cache explain <module>`

Reports source SHA, ActionDigest, compiler identity, dependency interfaces, macro root,
AOP root, resolution witness, which field caused a miss, whether SHA was stamp-reused or
freshly computed, and whether result came from memory / local disk / remote CAS.

## Part 2 — Hole remediation, migration, compatibility, regression tests

### 2.1 Remediation (by priority — from audit §5)

**P0**
- Interp module cache: split into session realization (ActionDigest) vs global immutable
  artifacts; hit path re-validates ActionDigest before reuse.
- Selective clear: validate retained stdlib/path-resolution entries against source/action
  digest instead of blanket-retaining.
- Path-resolution cache: replace bare `u64` with full typed key + resolution witness
  (ordered probed candidates, per-candidate existence, selected, parent-dir generation,
  resolver policy/version); bound negative-cache TTL.
- Macro contracts: re-key by qualified stable macro ID + definition/read-set digest
  (definition + invocation layers, §1 of audit).
- SMF mmap + loaded-module caches: resolve path → immutable `ArtifactId`; compare IDs.
- Make action-manifest verification mandatory before any cache admission.
- Record semantic read sets + aspect-selection roots so new applicable macros/aspects
  invalidate.

**P1**
- Reject zero-options-hash SMFs from global admission (local compat only; rebuild first).
- `validated_smf_load`: actually compare stored source SHA / ActionDigest to current input.
- Replace custom text semantic hash with SHA-256 over canonical sorted binary encoding.
- Self-hosted load-session: generation-aware target/freshness entries, or invalidate all
  related indexes together.
- Library getter: in-memory reader or digest-qualified private temp (drop
  `/tmp/smf_getter_<module>.smf`).
- Disk cache paths: digest paths or escaped structured components (stop `/`→`_` collisions).

### 2.2 Migration

1. Land the four-identity digest layer + canonical binary encoder (no behavior change;
   compute-and-log only, `--cache-explain` observability).
2. Introduce process-global immutable cache behind a flag; keep existing per-thread caches
   as fallback; A/B correctness compare via `--cache-strict` shadow lookups.
3. Add disk CAS + action cache (write-through; reads still verified by digest).
4. Flip default resolver/loader to `ArtifactId` comparison; path becomes alias.
5. Add SMF manifest emission to the producer; readers accept manifest-less as compat input.
6. Cut interpreter realization over to "global plan → fresh session instance".
7. Retire legacy path-keyed caches once shadow-compare shows zero divergence.

### 2.3 Compatibility

- Manifest-less / zero-hash SMFs: accepted as local input, never served from trusted
  global cache; regenerated when source is available.
- `$SIMPLE_CACHE` schema versioned; on schema bump, ignore (don't trust) old entries.
- Bootstrap/CI pin `--cache-strict` (mode A) so a cache bug can never mask a real diff.

### 2.4 Regression tests (each hole → one runnable check)

- **Path false-hit:** load module, replace bytes at same path, assert new `ArtifactId` +
  re-realization (not stale hit).
- **New-file resolution:** create a higher-priority candidate after a negative resolution;
  assert re-resolution via witness (directory-generation bump).
- **Same-name macro:** two modules define same macro name, different contracts/scope;
  assert distinct `MacroDefinitionDigest`, no cross-reuse.
- **Macro hygiene:** cached pre-hygiene template applied twice; assert fresh gensym IDs.
- **AOP body-only:** change advice body, unchanged interface; assert caller NOT re-woven
  but linked image binds new impl.
- **AOP interface/pointcut change:** assert re-weave + relink.
- **Imported aspect:** add applicable aspect in imported module, target source unchanged;
  assert target invalidated (aspect-set digest changed).
- **SMF stale:** older SMF vs newer source rejected; zero-options-hash rejected from global
  admission.
- **Strict-mode parity (A):** `--cache-strict` full rehash must produce identical
  ActionDigests to stamp-fast C on an unchanged tree; any divergence fails CI.
- **Disk CAS integrity:** corrupt a CAS blob; assert digest-mismatch detection on read.
- **Import cycle:** cyclic modules produce stable `SCCDigest` across runs.
- **Cross-process:** two processes share a warm disk CAS; assert identical realized output.

### 2.5 Sequencing note

Do NOT attempt the red-green query engine (Option D) here. Land C's identity layer,
dependency manifests, and the session/global boundary first; D becomes viable only once
those are correct.
