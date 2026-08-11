# test/ Manifest

Test suites organized by numbered category.

## Allowed Entries

| Entry | Description |
|---|---|
| `00_formal_verification` | Formal verification (Lean proofs, memory safety) |
| `01_unit` | Unit tests |
| `02_integration` | Integration tests |
| `03_system` | System tests (includes feature tests) |
| `04_smoke` | Smoke tests |
| `05_perf` | Performance tests |
| `06_fuzz` | Fuzz tests |
| `07_security` | Security tests |
| `08_web_platform` | Web platform conformance tests |
| `09_baselines` | Baseline snapshots |
| `unit` | MIRROR of `01_unit` (partial subset) — do NOT author new specs here |
| `integration` | MIRROR of `02_integration` (partial subset) — do NOT author new specs here |
| `ci` | CI test configurations |
| `fixtures` | Test fixtures |
| `shared` | Shared test utilities |
| `README.md` | Test readme |
| `FILE.md` | This manifest |

## Canonical vs mirror trees

`test/01_unit/` and `test/02_integration/` are CANONICAL. `test/unit/` and
`test/integration/` are legacy MIRRORS (deliberate partial subsets). New specs
go into the canonical tree; a file that exists only in a mirror tree is treated
as authored-into-the-wrong-tree and FAILS the pre-push guard
`scripts/check/check-test-tree-divergence.shs` unless it has a reviewed entry in
`scripts/check/test_tree_mirror_only_allowlist.txt`.
