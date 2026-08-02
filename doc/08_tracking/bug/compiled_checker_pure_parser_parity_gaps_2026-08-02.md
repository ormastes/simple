# Compiled checker pure-parser parity gaps

## Status

Open, P1.  The compiled checker rejects 247 individually reproduced repository
sources that use canonical language surfaces represented in the Rust parser,
while 147 other individual failures are demonstrably invalid source and 17 are
intentional SSpec check-surface rejections.

## Reproduction

```bash
python3 scripts/check/compiled-check-tree.py \
  --checker=/absolute/path/to/simple-check \
  --root=src/compiler --root=src/app --root=src/lib \
  --output-dir=build/mini_builds/full-tree-compiled-check-bounded-cycle1 \
  --workers=4 --batch-size=64 --timeout=120

python3 scripts/check/classify-compiled-check-results.py \
  --evidence-dir=build/mini_builds/full-tree-compiled-check-bounded-cycle1
```

Artifact SHA-256:
`27b9593a697d7115b9e16b4471b33f969bd98229e410a866c2ef28d3d95c6874`.
Manifest: 11,433 files, digest
`4522a42023807eabb45c24dc8c7f31b590c7640d717f83d554e954947b413298`.

## Evidence and owners

The highest-volume parser routes are type/multiline signatures (62), class
members (51), metadata blocks (24), unmatched canonical surface (20), keyword
identifiers (18), and structured/keyword exports (17).  Exact per-file routing
is retained in the build evidence and compact group routing in
`doc/03_plan/compiler/bootstrap/compiled_checker_failure_routes_2026-08-02.tsv`.

Likely owners are the pure-Simple parser declaration/type/expression surfaces
under `src/compiler/10.frontend/core/`, with the Rust parser serving as the
canonical parity reference.  Fix categories separately and rerun the immutable
manifest checker; do not modify invalid source merely to hide a parser gap.

## Non-cause

Batch parser-state leakage was investigated and disproved by a two-file minimal
pair.  The aggregate checker correctly reports one failing file of two; passing
members of a nonzero batch are not false positives.

