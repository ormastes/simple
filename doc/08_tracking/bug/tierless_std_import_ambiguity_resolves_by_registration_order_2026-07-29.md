# Tier-less `use std.X` imports resolve by registration order, not by tier

**Status:** stage 1 landed — the resolver now emits a default-on, NON-FATAL
warning when a tier-less `use std.<path>` resolves via the `lib/*/` tier
search and the path exists under 2+ tiers, naming the candidate tiers
(`maybe_warn_tier_ambiguity` in
`src/compiler/99.loader/module_resolver/resolution.spl`). Deduplicated to
once per distinct path per compilation; `SIMPLE_AMBIGUOUS_IMPORT_WARN=0`
silences, `=verbose` warns per occurrence. Tier-multiplicity map is built
lazily once per lib dir. Resolution behavior is unchanged. Stages 2
(deterministic precedence) and 3 (error) remain open.
Spec: `test/01_unit/compiler/module_resolver/tier_ambiguity_warning_spec.spl`.
One instance fixed earlier (`552b5a335b2`).
**Severity:** silent wrong-symbol selection. Diagnostic now emitted (stage 1).

## Mechanism

`src/lib/` is split into tiers: `common`, `nogc_sync_mut`, `nogc_async_mut`,
`gc_async_mut`, `nogc_async_mut_noalloc`. A module path may exist under several
of them. An import written **tier-lessly** as `use std.<path>` does not say which
tier it means.

Same-named types from different modules then collapse in the global registry,
and **whichever registers first wins for every importer**. This is already
documented in-tree at `src/compiler/70.backend/backend_types.spl:104-113`, where
a `CompiledSymbolKind` collision produced
`unknown variant or method 'Const' on enum CompiledSymbolKind`.

Because resolution depends on registration order, an unrelated edit elsewhere
can silently change which symbol a file gets.

## Confirmed instance (fixed)

`src/lib/common/ui/capability_policy.spl` imported `use std.security.types.{...}`.
Two declarations of `enum SecurityEvent` exist with **different variant sets and
a different arity on a shared variant name**:

- `src/lib/common/security/types.spl` — 5 variants incl. `CapabilityDenied`
- `src/lib/nogc_sync_mut/security/types.spl` — 10 variants

Symptom: `mir: unknown variant 'CapabilityDenied' on enum SecurityEvent`.
Fixed in `552b5a335b2` by qualifying the import as `std.common.security.types`.

**`security/types.spl` actually exists in FOUR tiers** (`common`,
`nogc_sync_mut`, `nogc_async_mut`, `gc_async_mut`) — the original report
understated it as two.

## Measured hazard surface (2026-07-29, `src/` + `test/`)

| Measure | Count |
|---|---|
| Module sub-paths duplicated across 2+ tiers | **1,553** |
| Distinct tier-less `use std.` paths | 1,699 |
| Distinct tier-less paths that are **ambiguous** | **437** |
| **Ambiguous import occurrences** | **21,445** |

Tier spread of the 437 ambiguous paths: 145 span 2 tiers, 281 span 3, 10 span 4,
1 spans all 5.

Most-imported ambiguous paths: `spec` (13,568), `spipe` (1,779),
`io_runtime` (1,305), `io` (411), `ndarray` (193), `log` (182),
`fs_driver.types` (137), `cli.cli_util` (132).

Reproduce:
```
for t in common nogc_sync_mut nogc_async_mut gc_async_mut nogc_async_mut_noalloc; do
  find src/lib/$t -name '*.spl' | sed "s|^src/lib/$t/||"
done | sort | uniq -d
```

## Why a call-site sweep is the wrong fix

21,445 occurrences is not a landable change, and qualifying every import would
not prevent the next one. The hazard is that the ambiguity is **accepted
silently**.

## Recommended fix — precedent already exists

The resolver **already errors on a different ambiguity class**
(`src/compiler/99.loader/module_resolver/resolution.spl:238-242`):

> `ambiguous import: module X resolves to both a file and a directory module;
> choose one of ... ` — with note *"rename or remove one form so the module path
> is unambiguous"*.

Tier ambiguity deserves the same treatment. Options, cheapest first:

1. **Warn** on a tier-less `use std.<path>` where `<path>` exists under 2+
   tiers, naming the candidates. Default-on, non-fatal — turns 21,445 latent
   sites into a ranked work list without breaking any build.
2. **Deterministic precedence** (e.g. importer's own tier, then `common`), so
   resolution stops depending on registration order even where ambiguous.
3. **Error**, matching the file-vs-directory precedent. Correct end state, but
   only after (1) has drained the list.

Until then, every ambiguous import is order-dependent, and the failure surfaces
as a wrong variant set or a wrong arity rather than a missing-module error.

## Related

- `src/compiler/70.backend/backend_types.spl:104-113` — same class,
  `CompiledSymbolKind`, with a hand-maintained "keep these identical" comment as
  the current mitigation.

## Narrowed 2026-08-01: it is not registration order when a root `src/lib/<name>/` exists

Measured for the `std.js.*` family and recorded in
`tierless_std_js_imports_resolve_to_root_lib_js_not_common_2026-08-01.md`.

The "resolves by registration order" framing does not hold for a tier-less path
whose head segment is also a real directory directly under `src/lib/`.
`_resolve_module_path_uncached` tries `src/` + the relative path (step 3)
*before* the tier search (step 4), so `use std.js.types.js_types` lands on
`src/lib/js/types/js_types.spl` deterministically, from every importer location
— including from inside `src/lib/common/js/`. Proved with a sentinel probe that
also reports `COMMON` and `NOGC_SYNC_MUT` when the import is tier-explicit, so
the harness discriminates.

Two consequences for the drain list:

1. The ambiguity is **worse** than order-dependence for these paths: it is a
   stable wrong answer, so it will not show up as flakiness and cannot be found
   by re-running.
2. The warning map in `99.loader/module_resolver/resolution.spl:262` walks only
   the five tier directories, so a path that collides with a **root**
   `src/lib/<name>/` module is never flagged at all. `std.js.*` is exactly that
   case: `src/lib/js/` holds 10 modules that shadow their `common/` and
   `nogc_sync_mut/` namesakes without warning.

Suggested addition to remediation step (1): include root-level `src/lib/<name>/`
directories in the multiplicity map, not just the five tiers.

### DONE 2026-08-17 — root-lib blindness closed (stage 1.5)

Reproduced first, on current source, with the new spec and the fix line
commented out: `Results: 3 total, 1 passed, 2 failed`. With the fix restored:
`Results: 3 total, 3 passed, 0 failed`; detection spec
`Results: 7 total, 7 passed, 0 failed`.

Root cause: `build_tier_multiplicity` walked only the five tier names, and
`maybe_warn_tier_ambiguity` was only called from the tier-search branch
(`resolution.spl:139`), never from the direct `src/lib/<path>` step
(`resolution.spl:99`) that actually wins for root modules.

Changes (all in `src/compiler/99.loader/module_resolver/resolution.spl`):
- new `collect_lib_root_modules`, recording every non-tier entry directly under
  `src/lib/` (dir package with `__init__.spl`, nested paths, bare `.spl` file)
  under the pseudo-tier `<lib-root>`; called from `build_tier_multiplicity`.
- the direct `src/lib/<path>` resolve step now calls
  `maybe_warn_tier_ambiguity` on its Ok path, still non-fatal, still before the
  cache write, resolution unchanged.
- the warning text says the root module wins deterministically (rather than "by
  registration order") when `<lib-root>` is among the candidates.

Specs: `test/01_unit/compiler/module_resolver/root_lib_shadow_ambiguity_spec.spl`
(reproducer) and `.../import_shadow_source_coverage_spec.spl` (defect-class
detection: three module shapes, a real `src/lib/text.spl` vs
`src/lib/common/text.spl` collision, and negative checks).

**Still open:** stage 2 (deterministic precedence by importer's own tier, then
`common`) and stage 3 (error). Not attempted here — changing which module an
ambiguous import binds is a behaviour change across 21,445 occurrences and was
out of scope for a diagnostic-only fix.

`src/lib/common/js/**` has been drained (30 files, 52 import lines) as part of
that work.
