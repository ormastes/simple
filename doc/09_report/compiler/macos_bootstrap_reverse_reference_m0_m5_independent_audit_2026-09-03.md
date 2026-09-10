# macOS Bootstrap Reverse-Reference M0–M5 Independent Audit

**Date:** 2026-09-03
**Audited integration HEAD:** `49eb1be4d5ae20c09937435bdfada11b19d21ea5`
**Host:** macOS 26.5, native arm64
**Verdict:** **NOT COMPLETE — structural gates pass; producer, Intel, and release authority are unavailable.**

This audit independently maps every M0–M5 implementation item and acceptance
gate in
`doc/03_plan/compiler/macos_bootstrap_reverse_reference_harmonization_plan_2026-08-30.md`.
Portable evidence is not promoted to native evidence.

## Executed gates

| Scope | Command | Result |
|---|---|---|
| M0/M1 receipt, target, SDK, provider, and linker contract | `sh scripts/check/check-macos-bootstrap-receipt.shs --portable` | **PASS** |
| M2/M3 compatibility and reuse invariants | `sh scripts/check/check-m3-phase2-phase3-mutations.shs .` | **PASS**, baseline plus **16/16** mutations rejected |
| M2 ten-family owner publication | `sh scripts/check/check-macos-reverse-reference-owner-publication-mutations.shs .` | **PASS** |
| M4 fixtures, tools, provider mutation, Results parser, workflow, and NFR policy | `sh test/01_unit/scripts/macos_reverse_reference_m4_contract_test.shs` | **PASS** |
| M5 hermetic snapshot and drift rejection | `sh test/01_unit/scripts/macos_m5_hermetic_snapshot_wrapper_test.shs` | **PASS**, **5/5** mutations rejected |
| Centralized storage production mutation guard | `sh test/01_unit/scripts/centralized_storage_roots_guard_test.shs` | **PASS** |
| Direct environment boundary | `sh scripts/audit/direct-env-runtime-guard.shs --working` | **PASS** |
| Executable-spec layout | `find doc/06_spec -name '*_spec.spl'` | **PASS**, zero files |

The Simple resolver spec could not execute because this isolated integration
checkout has no admitted non-seed runtime. The wrapper at `bin/release/simple`
fails closed rather than selecting an unadmitted binary. No seed or raw-source
fallback was used.

## M0 — baselines and receipts

| Requirement | Determination | Evidence or missing authority |
|---|---|---|
| Native arm64 cold Phase2/3 baseline | **BLOCKED** | No producer-authenticated Stage2/Stage3 pair or admitted architecture baseline exists. |
| Native x86_64 cold Phase2/3 baseline | **BLOCKED** | No Intel artifact or native Intel runner execution is available. |
| Wall, CPU, peak/retained RSS, cache/work/source-read counts | **STRUCTURALLY REQUIRED; NATIVE MISSING** | M4/performance validators fail closed, but no qualifying producer run exists. |
| Exact compiler/provider/SDK/target/command hashes | **STRUCTURAL PASS** | M0/M1 portable checker passes and M4 requires each field. |
| Receipt validates live immutable bytes | **STRUCTURAL PASS** | Portable checker and mutation contracts bind live artifact bytes and reject mismatches. |

**M0 gate:** incomplete because neither required architecture has an admitted
Phase2/Phase3 baseline receipt pair.

## M1 — target and linker correctness

| Requirement | Determination | Evidence or missing authority |
|---|---|---|
| Darwin target, deployment target, SDK, Xcode/Clang, and linker identities enter action/admission keys | **STRUCTURAL PASS** | M0/M1 portable checker passes. |
| Darwin uses `-dead_strip` and excludes ELF hardening | **STRUCTURAL PASS** | Linker policy is checked by the portable logic and M4 contract. |
| Runtime/provider archives are Mach-O and match the requested slice | **STRUCTURAL PASS; NATIVE MISSING** | Validation exists; no admitted arm64/x86_64 provider archive pair exists. |
| Architecture, SDK, provider, deployment, and live-byte mismatch rejection | **STRUCTURAL PASS** | Negative checks are present and mutation-sensitive. |

**M1 gate:** implementation is present; two-architecture native proof is absent.

## M2 — reverse-reference projection receipts

| Requirement | Determination |
|---|---|
| Versioned `ReverseReferenceKeyV1`, owner/root generations, projection kind/digest, and schema | **STRUCTURAL PASS** |
| Immutable generation receipt | **STRUCTURAL PASS** |
| Ten distinct owner families: imports/exports, traits, unresolved methods, annotations, generics, AOP, runtime providers, initializers, module/SCC, relocations | **STRUCTURAL PASS** |
| Private-body interface cutoff and exact exported-interface consumers | **STRUCTURAL PASS** |
| SCC/transitive closure remains distinct from ordinary import consumption | **STRUCTURAL PASS** |
| Missing/unknown/corrupt state emits attributed conservative fallback | **STRUCTURAL PASS** |
| Causal positive, negative, boundary, and corruption native receipts | **NATIVE BLOCKED** |

The owner-publication checker passes and the M2/M3 matrix rejects all 16
weakenings. No native incremental execution receipt is available.

## M3 — Phase2 to Phase3 compatible reuse

| Requirement | Determination |
|---|---|
| Phase2 and Phase3 writable caches remain separate | **STRUCTURAL PASS** |
| Read-only compatibility manifest binds exact M2 receipt, generations, consumer, provider, target, schema, and artifact | **STRUCTURAL PASS** |
| Canonical no-follow reads and exclusive immutable publication | **STRUCTURAL PASS** |
| Every reuse/rejection has an attributed ledger decision | **STRUCTURAL PASS** |
| Clean and reused outputs use only documented normalization | **STRUCTURAL PASS; NATIVE COMPARISON MISSING** |
| No-op has zero parse/lower/emit and zero link when ordered inputs are unchanged | **RED / NATIVE MISSING** |
| Private-body and interface edits rebuild only proven closures | **STRUCTURAL PASS; NATIVE MISSING** |

**M3 gate:** no admitted producer-created Stage2→Stage3 chain exists, so no
native hit/rejection ledger or output-equivalence receipt can be accepted.

## M4 — native per-architecture qualification

The portable contract proves the exact eight fixtures, strict nonzero
`Results:` parsing, producer-built CLI/test/MCP/LSP tools, provider/archive
mutation, no-op/private/interface/provider/linker/corrupt/interrupted work
evidence, and architecture-matched RSS policy.

| Native row | Determination | Missing prerequisite |
|---|---|---|
| arm64 | **BLOCKED** | Producer-authenticated Phase3 candidate, admission receipt, authority receipt, and admitted residency baseline. |
| x86_64 | **BLOCKED** | Native Intel runner plus the same producer and baseline artifacts. Rosetta is not acceptable evidence. |

**M4 gate:** portable contract **PASS**; native qualification **not run**.

## M5 — universal packaging and promotion

| Requirement | Determination |
|---|---|
| Exact immutable three-file portable snapshot | **PASS** |
| Source/snapshot drift rejection and undeclared-file exclusion | **PASS**, 5/5 mutations rejected |
| Compose only two admitted thin Phase3/M4 slices | **BLOCKED** |
| Execute unsigned universal natively on arm64 and x86_64 | **BLOCKED** |
| Distribution sign, notarize, staple, Gatekeeper-assess, and rerun both native rows | **AUTHORITY BLOCKED** |
| Promote tested digest without rebuild and retain rollback receipt | **BLOCKED** |

The host has `codesign`, `xcrun`, and `lipo`, but `security find-identity -p
codesigning` reports **0 valid identities**. The `SIMPLE_NOTARY` keychain-profile
probe exits 69. Tools alone are not release authority.

## Centralized-storage audit and repairs

The migration initially left M2–M5 qualification scratch and evidence under
ambient `/tmp` or repository `build/` paths. The audit repaired:

- M2/M3 and owner-mutation scratch through `storage_roots_mktemp`;
- M4 default evidence, self-test scratch, workflow-readiness scratch, and
  long-lived residency evidence under `SIMPLE_WORKTREE_STORAGE_ROOT`;
- M5 hermetic driver scratch, default evidence, self-test scratch, and blocked
  receipts under `SIMPLE_WORKTREE_STORAGE_ROOT`;
- M4/M5 workflows by declaring `${{ github.workspace }}/build` as their
  worktree storage root, preserving existing artifact paths without creating a
  third root;
- bootstrap help text to name the centralized default rather than stale
  `build/bootstrap`;
- a macOS case-insensitive marker defect: legacy
  `~/Library/Caches/Simple/storage` markers are authenticated and atomically
  normalized to canonical `~/Library/Caches/simple/storage`. Unrelated marker
  mismatches still fail closed.

After repair, all shell gates listed above pass. No remaining isolated M0–M5
source or harness defect was found in this audit.

## Exact blocker manifest

### Producer artifacts unavailable

The last production attempt passed disk preflight and then failed before
Stage2 because this checkout has none of the authenticated runtime tuple:

```text
src/compiler_rust/target/bootstrap/simple
src/compiler_rust/target/bootstrap/libsimple_native_all.a
src/compiler_rust/target/bootstrap/libsimple_compiler_backfill.a
```

The admitted arm64 executable at
`/Users/ormastes/simple/bin/release/macos-arm64/simple` does not authenticate
replacement archives. Copying artifacts or synthesizing receipts is forbidden.
Once an external producer publishes the authenticated tuple and its hosted
runtime receipt, run:

```sh
SIMPLE_BUILD_COMPILER=/Users/ormastes/simple/bin/release/macos-arm64/simple \
SIMPLE_BINARY=/Users/ormastes/simple/bin/release/macos-arm64/simple \
scripts/bootstrap/bootstrap-from-scratch.sh \
  --pure-simple --stop-after-stage3 --jobs=1 --no-mcp
```

The default output is
`$SIMPLE_WORKTREE_STORAGE_ROOT/build/bootstrap`; do not pass a legacy output
unless its receipt explicitly records that override.

### Native M4 inputs unavailable

For each architecture, obtain an attested Phase3 artifact bundle, exact source
workflow run/attempt, and admitted residency-baseline artifact. Then dispatch:

```sh
gh workflow run macos-reverse-reference-m4.yml \
  -f requested_arch=<arm64|x86_64> \
  -f runner_label=<native-runner-label> \
  -f source_run_id=<phase3-run-id> \
  -f source_run_attempt=<phase3-attempt> \
  -f source_revision=<exact-sha> \
  -f phase3_artifact=<artifact-name> \
  -f residency_authority_run_id=<baseline-run-id> \
  -f residency_authority_artifact=<baseline-artifact>
```

The x86_64 row additionally requires an actual native Intel runner label.

### M5 and release authority unavailable

After both M4 runs and evidence artifacts are admitted, dispatch:

```sh
gh workflow run macos-reverse-reference-m5.yml \
  -f source_revision=<exact-sha> \
  -f arm64_run_id=<run> -f arm64_run_attempt=<attempt> \
  -f x86_64_run_id=<run> -f x86_64_run_attempt=<attempt> \
  -f arm64_artifact=<artifact> -f x86_64_artifact=<artifact> \
  -f arm64_evidence_artifact=<artifact> \
  -f x86_64_evidence_artifact=<artifact> \
  -f arm64_runner=<native-arm64-label> \
  -f x86_64_runner=<native-intel-label> \
  -f expected_current_digest=<NONE-or-current-digest>
```

Finalization additionally requires an installed Apple Developer ID signing
identity and a valid notarization keychain profile. Their absence cannot be
repaired in source.

## Final determination

- **Actionable source/harness gaps:** found and repaired; focused shell evidence passes.
- **Producer-bound arm64 evidence:** unavailable.
- **Native x86_64 runner and evidence:** unavailable.
- **Apple signing/notary authority:** unavailable.
- **M0–M5 completion:** **FAIL / NOT COMPLETE**.
