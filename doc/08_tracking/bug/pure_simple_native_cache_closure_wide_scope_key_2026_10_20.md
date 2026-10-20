# Pure-Simple native-build object cache is keyed on the whole source closure

- Status: FIX LANDED (key functions); native evidence pending next Stage 2
- Date: 2026-10-20
- Related: the seed object-cache keying lane (Opus) fixes the same symptom on
  the Rust seed's native_project path; this record is the pure-Simple twin.
- Blocks: "recompile only affected objects and relink" for compiler
  rebuilds done with a pure-Simple (Stage 2/3) compiler, and therefore the
  self-hosted rebuild route (Stage 3 rebuilding Stage 3).

## Observation

- `.claude/rules/bootstrap.md` ("Layer 2", 2026-08-08): the pure-Simple
  driver hashes the entire loaded source closure into `cache_scope_root`, so
  editing any one file changes the scope directory and drops reuse to 0
  for every module (measured 3/3 reused unchanged, 0/3 after a one-line edit).
- Same symptom on the seed path today: relinking the r14 Stage 2 after a
  two-file change (83ff46b0bc4) reported `compiled=1367 reused=0` both
  against the read-only admitted cache and against a writable copy
  (`scratchpad/cache14w`, 1645 objects): 285 s and 196 s for a full
  recompile instead of a relink.

## Expected

Per-module keys over the module's own source plus its imported interface
digests (`action_key.spl:interface_digest_of` already exists), so an edit
recompiles the edited module and its dependents only.

## Root cause (measured 2026-10-20, r16b admitted Stage 2, aarch64)

The scope directory is no longer closure-keyed: the cache root is stable and
each object is admitted by a per-module witness (own MIR identity, direct
dependency interface facts, resolution traces, cross-module layouts, config).
But a 4-module probe (`main -> mid -> prov`, `main -> other`) rebuilt with
NO edit still reported `Cache: reused 0 modules; rebuilt 4.` for three
reasons:

1. **Importer witnesses were always refused.** Surfaces look a dependency
   up by `module_surface_canonical_path` (absolute). The source interface
   index is keyed by the loaded path, which is relative. Every lookup
   missed, and every importer got `ambiguous-dependency-source`. This is
   in the shadow receipt `module=pscache_probe.main reason=ambiguous-dependency-source`.
   **Fixed:** the index also keys facts by canonical path. Two raw
   spellings of one file with different facts stay refused.
2. **Dependency facts under-captured fields.** `interface_digest_of_source`
   skips struct field lines, so a provider field add, reorder or retype
   left the importer's witness unchanged. Only a layout trace could save
   it, so this was a potential stale hit. It also captured every `use`
   line, so an import added for a body rebuilt every importer.
   **Fixed:** `cache/native_interface_slice.spl` keeps ordered
   declarations and keys each importer on the slice it imports, closed
   over the identifiers inside it.
3. **Without an ABI admission the compiler identity is per run**
   (`native_build_uncacheable_abi_identity`). This is by design. A probe
   must set `SIMPLE_ABI_POLICY=v1` and `SIMPLE_ABI_ADMISSION_RECEIPT`.

Still open: `driver_native_frozen_source_lookup` refuses a path that is
loaded under two module names (the probe's `prov` and `pscache_probe.prov`).
Those modules stay uncacheable. Fixing it needs BuildCache entries keyed by
module and path.

Specs: `test/01_unit/compiler/driver/native_module_cache_key_granularity_spec.spl`
(red 2/9 -> green 9/9; review cases added red -> green, 11/11). Native evidence of the fix needs a Stage 2 built
from this change; r16b only shows the pre-fix behaviour.
