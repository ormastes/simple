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
