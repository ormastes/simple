# Per-file rebuild soundness — evidence and verdict (2026-08-23)

**Status: DEMOTED to future work.** This study was commissioned to unblock
per-file incremental rebuild for the stage1 pipeline. The design changed
mid-flight to a two-mode build (convergence mode iterates on the failing set and
DISCARDS its output; validation mode is a clean full rebuild and is the only
artifact that ships). That change dissolves the blocker rather than solving it:
convergence mode does not need sound caching, only cheap monotone progress, and
validation mode does no reuse at all. This document is therefore recorded as
evidence for a possible later program — **sound per-file reuse for a DELIVERED
artifact** — and is not a prerequisite for anything currently planned.

**Verdict: per-file HIR reuse is UNSOUND today.** Do not key HIR entries on a
per-module import-closure digest. The evidence below is why.

## 1. The dependency is genuinely whole-program, not import-closure

`build_surface_decl_index`
(`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:351-384`) loops
`while surface_index < self.module_surfaces.surfaces.len()` over all six
declaration kinds and builds `{decl_name: [surface_index]}` into
`self.surface_decl_owners`.

"Every frozen surface" means the entire `ModuleSurfacesByName` registry, i.e.
the WHOLE program set — **not** the current module's import closure. The caller
chain confirms it: `hirlowering_for_module(_with_diagnostics)`
(`.../hir_lowering/types.spl:491-500`) assigns
`lowering.module_surfaces = module_surfaces`, and the driver passes
`retained_module_surfaces` — `ctx.module_surfaces`, else
`module_surfaces_from_modules(self.ctx.modules, self.ctx.sources)` —
at `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:490-493`. The same
single registry is used for both the bootstrap lowering (`:510`) and the
per-module lowering (`:560`).

## 2. There is no import-visibility filter at either lookup site

`surface_decl_owner_indices(name)` (`module_lowering.spl:386-395`) lazily builds
the index and returns `self.surface_decl_owners[name]` or `[]`. Two call sites,
neither filtered by import visibility:

- `_Items/module_import_registration.spl:576`, in
  `try_register_bootstrap_global_symbol`: `if owner_indices.len() != 1: return
  false`, otherwise `register_imported_symbol(matching_index, ...)`. **The
  behaviour is a function of the GLOBAL owner count.** Adding a same-named
  declaration in a never-imported, unrelated file flips `len() == 1` to
  `len() == 2` and the name silently fails to bind. Symmetrically, a
  non-imported surface is freely imported-from whenever its name is unique.
- `_Items/module_reexport_materialization.spl:854`, field/type package-dependency
  materialization. Candidates are filtered only by
  `candidate.module_name != imported_mod.module_name` and
  `cached_surface_package_name(candidate.module_name) == package_name` — a
  *package* filter, not an import filter. Ambiguity again gives up
  (`selected = -1`). The result is memoised in `field_package_dep_memo`, keyed by
  module + package + dependency.

So an edit to a sibling that a module never imports can change what that module
lowers to, while the module's own source and its import-closure digest are both
unchanged. That is a silent miscompile, which is strictly worse than a slow
build.

## 3. The current key is already whole-program, deliberately

`hir_cache_closure_digest` (`src/compiler/80.driver/driver_hir_cache.spl:84-109`)
folds `canonical_path | content_hash | content_length | module_name |
logical_name` for **every** frozen surface;
`hir_cache_key = sha256(sha256(source) \n closure_digest \n entry_flag \n
env_switches + hir_codec_header)`. The header comment at `:10-19` documents this
exact hazard as the reason the key is whole-program rather than per-import.

The cost of that correctness is total: any source edit anywhere invalidates every
entry. That is the real problem a future program would need to solve — and it is
a *precision* problem, not a *soundness* one. Today's key errs safe.

## 4. `interface_digest_of` is not a drop-in replacement

`src/compiler/80.driver/cache/action_key.spl:195-201` —
`sha256_text(canon_field("simple/interface/v1", canon_seq(items)))` over sorted
parts, with `struct ActionDep: module_id: text; iface_digest: text` at `:31-33`.
Its own comment at `:204+` warns that the textual v1 extractor misses
struct/class FIELD lines — an under-capture that can produce stale HITs — and
states that the HIR closure digest may NOT be re-keyed onto it. That warning is
independent of, and additional to, the cross-surface hazard above.

## 5. The hazard is not theoretical — measured

Census of top-level `fn` / `struct` / `class` / `enum` / `trait` declarations
across `src/compiler` and `src/lib` (unique name x file pairs):

| metric | value |
|---|---|
| distinct declaration names | 57,047 |
| names declared in more than one file | **7,206 (12.6%)** |

Examples: `resolve` (5 files), `ptrace_continue` (3), `value_clone` (3),
`render_lsp_html` (3), `make_span` (2), `IndexManager` (2).

One in eight names is already multiply-declared. The `len() != 1` bail-out at
`module_import_registration.spl:576` is therefore live, load-bearing behaviour
that a per-module key would silently desynchronise from.

## 6. If this is ever resumed

Three options, in increasing order of value and cost:

- **(a) Fold the declared-sibling name set into the key** alongside
  `interface_digest_of`. Sound, but the name set is nearly as broad as the
  closure digest it replaces, so the precision gain may not repay the work.
  Measure the name-set digest's invalidation rate against the closure digest's
  before building it.
- **(b) Make name lookup import-scoped** at both sites, so the cross-surface
  dependency disappears at the source. This is the only option that actually
  *removes* the hazard rather than encoding it. It is a semantic change to name
  resolution and needs its own compatibility study — the `len() != 1` bail-out is
  observable behaviour and 12.6% of names can reach it.
- **(c) Prove the cross-surface path is reachable only for a bounded, detectable
  class.** The census above is the argument against: 7,206 names is not a bounded
  class.

Recommendation if resumed: **(b)**, and only with a compatibility study first.
Do not attempt (a) without first measuring that it buys real precision.

## Non-goals

This document does not justify any reuse in validation mode. Validation mode
clears all caches and rebuilds from scratch by construction; that is what makes
the two-mode design safe without this study.
