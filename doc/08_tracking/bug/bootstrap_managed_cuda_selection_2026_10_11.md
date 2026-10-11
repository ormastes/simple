# Managed bootstrap CUDA selection

Status: scoped command/identity controls verified; native manager integration pending.

`bootstrap-from-scratch.sh` selects CUDA from `src/compiler/simple.sdn`, creates
an overlay keyed by manifest and template SHA-256, and puts it before ordinary
plugin source roots. Managed and provisional Phase 3/4 binary/object jobs were
missing this argument, allowing the ordinary static backend to win regardless
of the selected policy.

The generated overlay is outside the sealed manager source inventory. Passing
its absolute path into an admitted job would introduce unadmitted source bytes.
The managed callbacks therefore select the same template inside the immutable
snapshot:

| Policy | First source root |
| --- | --- |
| disabled | `src/compositions/cuda_disabled` |
| enabled/static | `src/plugins` |
| enabled/dynamic | `src/compositions/cuda_dynamic` |

Both the manifest and selected template must be regular inventory members.
Their digests form `cuda-<manifest-sha>-<template-sha>`, matching the generated
overlay identity. This identity is in the cache argument of the compiled task
manifest and a replay-checked `cuda-selection.env` beside that manifest. The
full source inventory also binds both input contents. Task IDs and receipt
paths remain stable.

Existing jobs without a selection record are refused without deleting their
cache. The managed runner regenerates and compares the complete task manifest
before reusing it; a retained manifest cannot silently omit the selector.
No source is filtered, no sealed source snapshot is modified, and no new external
source root is admitted. Object output validation and phase completion gates
remain authoritative.

Evidence: `scripts/bootstrap/tests/managed-cuda-selection-test.shs` passed.
It executes the actual extracted callback functions from both production
runners for all three modes, captures the manifest compiler arguments, and
checks first-root ordering, explicit target/object arguments, cache identity,
and selection records. It deliberately stops at manifest generation; it never
creates compiler outputs or claims native compilation success.

The same fixture proves manifest/template identity changes, missing inventory
membership, invalid policy, and legacy task manifests fail closed. Retained
fixture evidence: `/tmp/simple-managed-cuda.FubxeI/`.

Shell syntax, whitespace checks, and the working environment-facade guard passed.
A complete manager-owned native run with the selected root, source-closure
receipts, and both backend target objects remains pending. This change does not
qualify the compiler, CUDA dynamic loading, or bootstrap PASS.
