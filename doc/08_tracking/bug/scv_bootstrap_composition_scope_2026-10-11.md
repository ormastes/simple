# BUG-SCV-BOOTSTRAP-COMPOSITION-SCOPE-20261011

Status: OPEN — source repair and regression specifications authored; rebuilt-producer
qualification pending. No native success is claimed.

GitHub: https://github.com/ormastes/simple/issues/3094

The canonical Stage2 attempt at source `070c82333c95893d294ea1128538c1d123d4bae0`
exited 1 before HIR with `SCV-E-ADMISSION: source-inventory-scope-unsupported`.
Its admitted producer SHA256 was
`e6447d0d10f2c8ae552b67da8420a7e581a22bb55f79e4d4e4d30b981f095811`, built
from source `a51194b96b5`. That source's `source_authority.spl` is byte-identical
to the failing request's source revision.

Evidence in `/home/yoon/dev/simple-release-phase3-20261011`:

- `build/bootstrap-parent-reuse-070c/logs/aarch64-unknown-linux-gnu/stage2-native-build.log`
- `build/bootstrap-parent-reuse-070c/stage3/aarch64-unknown-linux-gnu/stage2-command.transcript`

The absolute K1 composition path belongs to `src` and is supported. The generated
`build/bootstrap-parent-reuse-070c/compositions/cuda-<manifest SHA>-<template SHA>`
path does not belong to the inventory's `src`/`test` event families. Allowing the
path prefix alone would still omit its ignored generated file from canonical
inventory selection; weakening admission would be incorrect.

The bootstrap constructor now retains generated CUDA bytes and identity evidence,
checks equality with the selected committed composition, and passes that canonical
root in all seven source-vector sites. A committed static composition mirrors the
existing default static template, with byte equality enforced before compilation.
Dynamic/disabled selection and K1 precedence remain manifest-driven.
Selected manifest/template/canonical hashes must also match the exact captured
source-before records used by existing bootstrap drift gates, including resumed
phase cache contexts; earlier live-file checks alone are not sufficient.

The pure-Simple alias adapter separately accepts a generated selector only after
validating its manifest/template SHA identities, mode, canonical bytes, generated
bytes, directory ownership and exact three-level membership. Snapshot selection
uses real canonical source rows plus the manifest; inherited workers revalidate
against frozen records and resolve inside the frozen composition namespace.
Arbitrary build trees, traversal, symlinks, changed bytes and additional generated
members are rejected. No generated inventory rows or live-source worker fallback
are introduced. Runtime/tool lineage remains the existing bootstrap authority's
responsibility and is not fabricated by this source-selector adapter.

Validation: focused shell constructor fixture controls and source inspections;
pure-Simple unit/integration specifications remain AUTHORED_UNEXECUTED until a
new admitted producer exists. Full compiler/lib/MCP checks and native bootstrap
qualification remain pending under the task's source-only execution restriction.
