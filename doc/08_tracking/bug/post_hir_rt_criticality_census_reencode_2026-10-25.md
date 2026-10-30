# Post-HIR root windows: rt_criticality census re-encode, nogc admission realpath (2026-10-25)

**release/1.0.0 port (2026-10-25):** only the snapshot-root rebase
(`7295342b8f7` + `ddc91a6e961`, reduced) applies on release. Fix 1 (census
re-encode skip, `709d74ec1bf`/`98df9caeb13`/`739eb007cc6`) has no target there:
release never carried the HIR-hit blob reuse (`59a5f999e92`), and `8c9d161def2`
made the per-module validation blob opt-in (`SIMPLE_HIR_VALIDATION_BLOBS=1`) with
an RT-policy short-circuit, so no cache-entry blob ever reaches the census.
Fix 2 (`e691d62fd83`) is superseded by release's own canonical-path caching
(`6cc26425011`/`7db42fe70fa`, `driver_nogc_param_effect_admission_v1`). On
release the rebase is a diagnostics-correctness fix (module.path, Span.file and
replayed warnings name the consuming snapshot), not a blob-reuse perf fix, and
there is no `rebound_hits` / hit-blob counter.

Status: fixed in source (`709d74ec1bf`, `e691d62fd83`); after-timing pending a Stage 2 rebuild.

## Symptom

Phase 3 native build, 1471 modules, HIR fully cache-adopted: the root process
spends 10+ minutes single-core between HIR done and MIR forking
(`log_build_step` markers, runs 23/24/25 under
`simple-boot-adhoc/build/phase3-ref`):

| window | run-23 | run-24 | run-25 |
|---|---|---|---|
| hir_post validate -> rt_criticality | 20 s | 24 s | 21 s |
| rt_criticality -> any_escape | 326 s | 353 s | 309 s |
| monomorphize -> mir_setup | 291 s | 111 s | 98 s |

Scaling on probes (same stage2, `--entry-closure`, warm/cold HIR cache):
rt window 3.9 s (114 modules) / 20.3 s (281) / 68.6 s (546 compiler modules).

## Root causes (gdb-sampled, stage2 sha256 `63262660...baf2be`, 546-module probe)

1. **rt_criticality window = pass-1 census only.** The tree has no `@rt` claims
   or HAL roots, so pass 2 returns early. Shares: 43% `hir_module_encode`
   (the canonical re-encode, `rt_criticality_validation.spl` census), 45%
   `rt_transient_array_scope_end` (per-blob scope teardown in the Rust runtime
   heap registry; the encoder's strings inflate it), 8% `hir_module_decode`.
   On a cache-adopted build every validation blob is the verbatim cache entry
   that the in-memory module was itself decoded from without a roundtrip, so
   the re-encode certified nothing downstream uses.
   Fix: the driver flags those blobs (`validation_module_blob_is_cache_entry`);
   the census skips only the re-encode for aligned, flagged blobs.
2. **validate window = O(n^2) realpath.** `driver_nogc_param_effect_admission_v1`
   called `module_surface_canonical_path` (realpath) inside its selection-sort
   inner loop (~1.1M syscalls at 1471 modules). 3/3 samples there (small n).
   Fix: canonicalize once per module.

## Behavioral delta (fix 1)

A decodable but noncanonical *cache* blob used to yield `[hir-blob-refused]`
plus the array fallback over the same decoded modules; it is now accepted as
the module that was compiled. Policy output is unchanged; the delta is
observability only (`[hir-blob-refused]` count was 0 in every phase3-ref run,
8..25). The "build proceeds UNCACHED" refusal text is prose that nothing
consumes, so no gating was lost.

Roundtrip coverage of cache entries: the store-side stability selfcheck
(`_hir_cache_selfcheck_due`) samples STORES (1 in 8 under `SIMPLE_BOOTSTRAP`),
and a fully cache-adopted run has zero stores. Before this change that run's
census re-encoded every flagged blob (100% witness); after it, 0%. Mitigation
already exists: `SIMPLE_HIR_CACHE_SELFCHECK=1` makes the load path use
`hir_module_decode_stable` (decode + re-encode + compare on every hit), and
`SIMPLE_HIR_CODEC_ROUNDTRIP=1` disables the flag entirely. Owner option, not
implemented: keep a sampled census re-encode (e.g. 1 in 8 flagged blobs).

## Engagement on the phase3-ref lane (statically confirmed: mostly NOT engaged)

`hir_cache_load_parsed_v1` clears the reusable hit blob whenever the stored
`module.path` differs from the consuming source path. Entries are keyed by a
repo-relative path digest, but the stored `module.path` (and every span file)
is the absolute SCV snapshot path of the run that stored it. Sampled
`phase3-ref/cache/hir` entries carry at least six different
`build/scv/snapshots/scv-revision-v1-<id>` prefixes; run-25 consumed from
`scv-revision-v1-4b49f891...`. So on a fully adopted run after any source
change, nearly every hit is a rebound hit: no hit blob, flag false, the census
still re-encodes, and the HIR loop also re-encodes the rebound module
(the `native_build_post_hir_root_serial_2026-10-24` reuse is defeated too).
Canonical-path comparison does not help: the directories genuinely differ.
Fix 1 engages only when the stored snapshot revision equals the consuming one.

Receipt: `phase3:hir:validate:rt_blobs cache_entry_blobs=<n> fresh_blobs=<m>
rebound_hits=<k>` (log_phase; needs `SIMPLE_COMPILER_PHASE_PROFILE=1`).
Owner options: store/compare repo-relative module paths (codec-visible
change: module.path and span files would no longer be absolute), or rebind the
path inside the stored blob (codec-layout dependent).

**Fixed (work/p3fix-hirpath, snapshot-root section):
rebase the blob before its one decode.** `hir_cache_snapshot_root_rebind_v1`
(driver_hir_cache.spl) reads the stored module.path (third blob line), and when
it and the consuming path are the same repo-relative file under two different
roots (old root non-empty, ends in `/`, re-join checked), the load replaces
`"\n" + old_root` with `"\n" + new_root` in the blob (and old->new in the stored
warnings) after the checksum and before decode. The codec is one escaped
scalar per line, so this rewrites exactly the text fields starting with the old
root: module.path and every Span.file, including other files of the same
snapshot. The decode is the module as lowered under the new root and the
patched blob is its canonical encoding, so the hit blob is kept (no re-encode
in the HIR loop or the census). Stored format unchanged -> no codec/cache
version bump. Fail closed: a rebase whose decode does not land the consuming
path is a `rebase` miss (own reject class). Only absolute, non-`/` roots rebase; relative (`../x/`) roots keep the rebound fallback. SIMPLE_HIR_CACHE_SELFCHECK=1 runs the stable
decode+re-encode on the patched blob. Receipt gains `rebased_hits=<n>`;
`rebound_hits` now counts only hits that still lost their blob.
Spec: `test/01_unit/compiler/driver/hir_cache_snapshot_root_rebind_spec.spl`.
Open for Stage 2: only proven under the seed runner. Acceptance is
`rebased_hits > 0` with `cache_entry_blobs` rising on a fully adopted run (the
helper uses two-arg `text.index_of`; if it misbehaves natively the rebase
silently never engages). Entries are never re-stored under the new root, so
every run rebases every hit (one `replace` per hit, untimed). `hir_cache_has`
does not rebase, so a rebase that fails closed is has=hit / load=miss (the
divergence class at the top of driver_hir_cache.spl; unreachable unless the
guards are wrong).

Follow-ups (review of 7295342b8f7, P2):
- Loaders that call `hir_cache_load_in_owned_scope` without `source_path`
  never rebase, so old-root modules persist there:
  `driver_hir_pipeline_lowering.spl:841`,
  `cache/hir_body_typecheck_lease_v1.spl:170`,
  `cache/hir_mono_archive_assembly_v1.spl:196`,
  `cache/hir_mono_archive_consumer_v1.spl:351`; the
  `module.path != input.source_path` refusals at
  `hir_body_typecheck_lease_v1.spl:115,139` remain.
- `module_source_relative_path` (`module_path_naming.spl:139`) cuts at the
  FIRST `/src/`: a repo checked out under a `.../src/...` directory gives a
  revision-dependent `rel`, so the rebase silently never engages there (falls
  back to the rebound path). Pre-existing.

Same class, not fixed here: the mono archive path refuses on
`module.path != source_path` (`mono_archive_registration_v1.spl:346`,
`hir_mono_archive_assembly_v1.spl:196`), and `forbidden_io_validation.spl:26`
compares module.path to a repo-relative literal. Codegen leak: with debug info
on, `core_codegen.spl:371` writes the first function's `span.file` into the
DIFile header, i.e. the absolute snapshot path -- objects differ per snapshot
revision (and, before this fix, also by whether the module was a cache hit
from an older revision). `mcdc_authored_path_v1(span.file)` reads the same
field. Native symbols already use `module_source_relative_path`.

## Open

- Monomorphize window not reproduced: probes give 0.27/1.2/3.8 s; the full
  closure takes 98-291 s, all inside `monomorphize_impl`. Needs
  `SIMPLE_COMPILER_PHASE_PROFILE=1` on a full run for `monomorphize:breakdown`.
- Owner decision: each cache-hit module is decoded twice (load, then census).
- Runtime: `rt_transient_array_scope_end` cost grows per module
  (34 -> 222 ms/module from 114 to 1471 modules); Rust runtime, not Simple.

## Acceptance (scheduled Stage 2)

Same probe and cache state with old vs new stage2: `rt_criticality ->
any_escape` and `validate -> rt_criticality` deltas; identical `sha256sum` of
the `-o` binary (arch_check_entry probe, rc=0), identical
`[WARN] any-escape pass: N` and `[mono]` lines, and the
`phase3:hir:validate:rt_blobs` receipt (a speed-up is only expected in
proportion to `cache_entry_blobs`).
