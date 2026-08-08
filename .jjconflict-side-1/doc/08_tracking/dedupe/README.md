# Spec-tree dedupe: prep, not deletion

`test/unit` and `test/integration` are stale mirrors of the canonical
`test/01_unit` and `test/02_integration` (`doc/07_guide/infra/testing.md:604-605,690`
maps `simple test --unit` to `test/01_unit/`).

**They were NOT deleted, and a blind delete would break things.**

## Why deletion is blocked

1. **CI runs them directly.** `.github/workflows/containerized-tests.yml`
   referenced the legacy paths at 8 sites.
2. **The runner supports them.** `test_level_detect.spl:8` calls
   `test/unit/`, `test/integration/`, `test/system/` the *"legacy bare mirror"*,
   and `test_runner_files.spl:98` handles it explicitly.
3. **The linter classifies by those prefixes.** `lint_cross_ref.spl:43-44`
   derives `is_unit` / `is_integration` from `test/unit/` and `test/integration/`.
4. **969 shared files differ in content** — 10.5% of the shared set, in both
   directions. Each is a merge decision, not a delete. Examples:
   `cli_parser_spec.spl` 4 lines vs 25; `native_build_arg_source_spec.spl` 22 vs
   37; `branch_coverage_7_spec.spl` 442 vs 442 with different content.
5. **22 files exist only in the legacy tree** and have no twin at all.

A 40-file sample suggested ~1-in-40 divergence; the full audit found 1-in-9.5.
Do not size this work from a sample.

## Full audit

| pair | old files | new files | shared | identical | divergent | old-only |
|---|---|---|---|---|---|---|
| `test/unit` vs `test/01_unit` | 8,312 | 10,440 | 8,290 | 7,414 | **876** | **22** |
| `test/integration` vs `test/02_integration` | 978 | 1,192 | 978 | 885 | **93** | 0 |

Counts are tracked files (`git ls-files`), not just `*_spec.spl` — the trees hold
fixtures and helpers too, which a spec-only comparison misses.

## Inventories

- `divergent_unit_vs_01_unit.txt` — 876 paths
- `divergent_integration_vs_02_integration.txt` — 93 paths
- `only_in_legacy_unit.txt` — 22 paths with no canonical twin

## Done in this change

Repointed the **5** CI references to `test/unit/std/arch_spec.spl` at
`test/01_unit/std/arch_spec.spl`. That file is **byte-identical** across trees
(`40d1d861` both sides), so this is provably a no-op in behaviour.

**Deliberately NOT repointed:** the 3 references to
`test/integration/log_facade_back_compat_spec.spl`. The two copies DIFFER
(`4b142373` vs `b499ec8c`), so repointing would silently change what CI tests
under a commit that claims only to move a path.

## Remaining order

1. Resolve the 969 divergences, or rule that the canonical tree wins and accept
   the loss deliberately.
2. Move the 22 legacy-only files into the canonical tree.
3. Repoint the 3 `log_facade` CI refs once its divergence is resolved.
4. Retire the runner's legacy-mirror handling and the linter's prefix branch.
5. Only then delete, in one sweep, with `--expect-files` — ~8,299 removals blow
   past the tree-size guard's +/-0.15% band.
