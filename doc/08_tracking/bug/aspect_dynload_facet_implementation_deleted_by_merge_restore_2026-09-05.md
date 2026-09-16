# The aspect/dynload facet implementation was deleted wholesale by a merge-restore

- **Filed:** 2026-09-05
- **Offending commit:** `fcbec1c3b625f073ddbc7f1faa72937346834bad`,
  `fix(merge): restore src/compiler and src/lib to origin for phase 1 bootstrap`,
  Thu Aug 27 23:49:50 2026 +0000
- **Severity:** high — a landed, executing compiler vertical slice is gone from
  `src/` with no bug record, and the docs still describe it as live

## What happened

That commit is a whole-subtree "restore to origin" of `src/compiler` and
`src/lib`. It is exactly the anti-pattern `.claude/rules/vcs.md` § "Sync must
never clobber" describes: a stale snapshot pushed over other sessions' landed
work. Among many other deletions it removed the entire closed-world facet
implementation:

| file | lines deleted |
|---|---|
| `src/compiler/10.frontend/facet_static_registry.spl` | 396 |
| `src/compiler/35.semantics/facet_static_binding.spl` | 177 |
| `src/compiler/35.semantics/facet_resolution.spl` | 858 |
| `src/compiler/80.driver/driver_facet_manifest_authority.spl` | 148 |
| `src/lib/common/facet_runtime.spl` | 484 |
| `src/compiler/99.loader/aspect_acquisition.spl` | 391 |
| `src/compiler/99.loader/aspect_final_unpin_registry.spl` | 177 |
| `src/compiler/99.loader/mcdc_aspect_pack_payload.spl` | 387 |
| `src/compiler/99.loader/mcdc_aspect_binding.spl` | 70 |
| `src/compiler/99.loader/mcdc_aspect_pack_activation.spl` | 44 |
| `src/lib/common/aspect_pack_lifecycle.spl` | 791 |
| `src/lib/common/aspect_pack_container.spl` | 701 |
| `src/lib/common/aspect_pack_catalog.spl` | 547 |
| `src/lib/common/aspect_pack_security.spl` | 113 |
| `src/lib/common/debug/aop_aspect_v1.spl` | 70 |

plus partial reversions of `10.frontend/aspect_registry.spl`,
`35.semantics/aspect_weave.spl`, `35.semantics/aspect_seal/facet_model.spl`
and `99.loader/aspect_pack_index_cache.spl`.

Recover any of it with `git show fcbec1c3b62^:<path>`.

## Evidence the deleted code was real and running

1. `doc/01_research/local/aspect_dynload.md:38` still states: *"Parser, HIR,
   MIR, and `validate_static_facet_bindings` support `.try_facet<F>()`; the HIR
   driver invokes the validator. **Compiler path is live.**"*
2. `test/01_unit/compiler/semantics/facet_static_binding_spec.spl` is written
   against concrete internals that only a real implementation exposes —
   `__facet_try$<Facet>` / `__facet_load$<Facet>` method names,
   `HirTypeKind.FacetRef`, `facet_static_method_symbol_matches`,
   `facet_static_resolved_route_id`.
3. `target/test-artifacts/01_unit/compiler/semantics/facet_static_binding/`
   exists — that spec executed at some point.
4. The deleted registry is not a sketch: it carries per-invocation declaration
   rows, reparse-scoped row eviction keyed on the declaring module, published
   resolved routes gated behind a post-HIR coherence pass, and exact HIR method
   identities with cross-module symbol provenance.

Today `grep -rn validate_static_facet_bindings src/` returns nothing.

## What this lane did instead, and why it is NOT the fix

`test/03_system/plan_acceptance/aspect_dynload_lane_plan_spec.spl` could not
load at all (`cannot resolve import compiler.frontend.facet_static_binding`).
To get it loading, minimal interface modules were landed at:

- `src/compiler/10.frontend/facet_static_registry.spl` (~70 lines)
- `src/compiler/10.frontend/facet_static_binding.spl` (~74 lines)

**These are placeholders and they occupy one of the clobbered paths.** They are
a tiny fraction of the deleted registry and implement none of the resolution,
coherence, or witness machinery. Restoring the real files must DELETE these
two, not merge with them. A partial restore was deliberately not attempted
here: `facet_static_binding.spl` depends on `facet_resolution.spl`, the
parser's `.try_facet<F>()` grammar and `HirTypeKind.FacetRef`, several of which
were reverted by the same commit, so restoring two files in isolation would not
build.

## Path discrepancy to settle during the restore

The two specs disagree about where the validator lives:

- `test/01_unit/compiler/semantics/facet_static_binding_spec.spl:10` imports
  `compiler.semantics.facet_static_binding` — which matches the deleted file's
  real home, `src/compiler/35.semantics/facet_static_binding.spl`.
- `test/03_system/plan_acceptance/aspect_dynload_lane_plan_spec.spl:74` imports
  `compiler.frontend.facet_static_binding`.

The deleted tree is authoritative: the validator belonged in `35.semantics`,
and only the *registry* was in `10.frontend`. The acceptance spec's import path
is therefore wrong and should be corrected to `compiler.semantics.` as part of
the restore — noted rather than edited here, because changing it now would only
move the load failure.

## Recommended action

Restore the deleted set from `fcbec1c3b62^` as one reviewed change, delete the
two placeholder files above, fix the acceptance spec's import path, and re-run
both specs. Audit the rest of `fcbec1c3b62` separately — the facet slice is
unlikely to be the only casualty of a whole-subtree restore.
