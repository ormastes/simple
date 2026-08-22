# Test-tree divergence delta step-over record (2026-08-22)

Landing: wave 4C/4D sspec modernization (75 + 72 files) + 26 twin syncs,
range origin/main(3fcb2e44)..<twin-sync commit>.

check-test-tree-divergence-delta.shs origin/main <NEW>:
PASS — 4 pre-existing offender(s), 0 introduced by this range
(base verdict counts: new + fixed-but-still-baselined + unallowlisted
mirror-only + stale-allowlist = 4; offender LISTS byte-identical at
BASE and NEW).

Pre-existing diverged-offender list (858 entries) preserved at
/mnt/data/tmp/test_tree_divergence_preexisting.txt and identical to the
committed baseline scripts/check/test_tree_divergence_baseline.txt
(854) plus 4 category offenders. No new divergence introduced.

## Wave-6 mod11 landing (2026-08-22)

Step-over (delta-PASS, 4 pre-existing offenders, none introduced by this range,
all already diverged at base 106dc4df58e):
- unit:app/llm_caret/agent_runtime_provider_spec.spl
- unit:compiler/hir/reexport_physical_cache_spec.spl
- unit:compiler/hir/resolve_import_symbols_spec.spl
- unit:compiler/semantics/collection_patterns_lint_spec.spl
