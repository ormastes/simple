# Remaining Phase-3 fixes ported to release/1.0.0

Base: `5b7cffc04b87fc1e2db729f7cec14de7f9a89f7e`.
Branch: `work/release100-phase3-remaining`.

This port retains the release branch's newer generic, borrow-check, visitor,
MMIO and imported-static implementations. It does not merge the older
30-commit migration branch or claim a successful Phase-3 qualification.

## Pattern annotation presence

Ported the constructor/default portion of `da90655df1e` as `e910495c701`.
The release base still declared `HirPattern.has_type_` without a default and
omitted it in untyped constructors. The port gives it a Boolean false default
and explicitly sets false at those constructors, including the newer release
`va_pat` construction in `switch_operators_calls.spl`. Typed and cloned
annotations retain their existing values.

The six-case SSpec covers the default, production lowering/desugaring,
absent/present codec round trips and authoritative absence. The older commit's
visitor/generator diagnostic change and negative diagnostic fixture are not
ported: release has a different visitor helper contract, and importing that
helper would require unrelated changes. Existing release visitor behavior is
unchanged, including its treatment of malformed present annotations.

Earlier migration evidence: rebuilt Stage-2 cold, cache-fill and cache-hit
`f07` object generation passed at `da90655df1e`; the later `1a1a95a7443`
campaign completed full-CLI and test-runner HIR without worker failures. That
evidence belongs to the earlier source lineage and does not qualify this port.

## Prescan binder lifetime

Ported `1a1a95a7443` as `e7db0371bb5`. `begin_module` now detaches
`prescan_type_parameters` immediately after resetting module symbol IDs;
archive-specific duplicate resets are removed. Retained phase memo state is
unchanged.

The original migration bug was exposed by a change that persisted bindings
from `lower_type_param`. The release implementation does not have that change:
it scopes prescan binders through imported-owner/field helpers. This port
enforces the module boundary for that existing map without changing its
same-module binding rules. Its tests therefore populate the map using release's
production `project_imported_owner_type_parameters`, then check same-module
resolution, recycled symbol IDs and transient detachment. The existing
`generic_field_prescan_spec.spl` empty-map assertion is preserved.

## Ownership-admission ordering

Ported `277f75dbde0`. Release still selection-sorted canonical module paths
inside a quadratic loop. The port computes each canonical key once and uses
stable index merge sorting, retaining equal-key input order and the existing
admission rounds and publication contract.

The implementation, focused SSpec, admission integration scenario and native
benchmark fixtures are carried over. The original five-pair native sorter
benchmark and its limits remain recorded in
[`phase3_post_hir_admission_quadratic_path_sort_2026_10_25.md`](../08_tracking/bug/phase3_post_hir_admission_quadratic_path_sort_2026_10_25.md).
Those measurements establish the old-lineage standalone sorter, not the new
release compiler's total time or memory. The old full-CLI timeout remained
after that optimization, so this port does not mark it resolved.

## Port validation and remaining gate

Static diff checks, working/staged direct-environment guards and executable
spec layout checks passed for the ported changes. No new full bootstrap or
SSpec runtime execution was performed in this port task. The exact final
branch requires review and relevant release-producer checks before a runtime
qualification claim. Old logs and producer identities are retained rather
than relabelled as evidence for this base.
