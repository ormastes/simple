# Feature: Stage 4 pure-Simple bootstrap

## Raw Request

`$sp_dev complete stage4_spdev.md`

## Task Type

bug

## Refined Goal

Produce, verify, and deploy the pure-Simple x86_64 Linux Stage 4 full CLI from
the current `main` revision without generated stubs, while preserving reusable
bootstrap caches and retaining exact progress, memory, provenance, sanity, and
essential-tool evidence.

## Acceptance Criteria

- AC-1: Every Stage 4 blocker edited in this lane is claimed in the canonical
  bug database before the edit, reproduced from the exact failing compiler and
  source revision, and resolved only after its fix and evidence are pushed.
- AC-2: The current imported-enum payload failure is fixed at its pure-Simple
  HIR/module-surface owner; no consumer-local import, facade payload re-export,
  Rust-seed change, generated stub, or source workaround is accepted.
- AC-3: Regression evidence reproduces the exact `MirInstKind` facade payload
  dependency route and at least one adjacent nested/aliased payload route while
  proving unrelated private symbols do not leak into the consumer.
- AC-4: The canonical Stage 3 bootstrap compiler is refreshed incrementally
  with `SIMPLE_NO_STUB_FALLBACK=1`; its provenance, version, command rejection,
  source admission, and non-stub log invariants pass.
- AC-5: One cache-preserving, full-resource Stage 4 build completes from the
  refreshed Stage 3 compiler and its retained progress record reaches the full
  module/task inventory with zero failed units.
- AC-6: The exact fresh Stage 4 candidate passes binary identity/provenance
  checks, `--version`, bounded arithmetic/run sanity, and the canonical
  redeploy admission gate without falling back to the Rust seed or a stale
  deployed wrapper.
- AC-7: `scripts/check/check-bootstrap-essential-tools-smoke.shs` passes once
  against that exact candidate and records
  `essential_test_runner_smoke=true`, `essential_lint_smoke=true`,
  `essential_duplicate_checker_smoke=true`, and
  `bootstrap_essential_tools_smoke=true`.
- AC-8: Deployment occurs only after AC-6 and AC-7, preserves the documented
  rollback behavior, and the installed binary hash equals the verified
  candidate hash.
- AC-9: `doc/03_plan/infra/agent_sessions/stage4_spdev.md` records the exact
  source revision, Stage 3 and Stage 4 paths/hashes, commands, cache receipts,
  progress/RSS logs, smoke markers, deployment result, rollback path, and any
  still-unavailable post-x86 platform rows.
- AC-10: Final verification reports zero executable `*_spec.spl` files under
  `doc/06_spec`, passes working/staged direct-env-runtime guards, contains no
  new placeholder/stub evidence, and receives normal/highest-capability review.

## Scope Exclusions

Native macOS, Windows, AArch64 Linux, and hosted RISC-V bootstrap execution are
not substituted by this Linux x86_64 build. Their acceptance rows remain active
handoffs under the authoritative Stage 4 plan. The separate ten-layer backend
artifact-debug feature is not Stage 4 acceptance evidence.

## Cooperative Review

- Correctness sidecar: isolated HIR/module-surface diagnosis and exact plus
  adjacent regression implementation.
- Performance sidecar: read-only progress/RSS/cache review; it must not edit the
  correctness owner or write the main bootstrap cache.
- Merge owner: primary Codex agent in the isolated integration worktree.
- Final reviewer: normal/highest-capability Codex after the exact candidate
  passes the essential-tools smoke.
- Shared pure-Simple interface names:
  `register_materialized_enum_payload_dependencies` and
  `resolve_materialized_enum_payload_origin`.
- Setup/checker helpers: canonical
  `scripts/bootstrap/bootstrap-from-scratch.sh` and
  `scripts/check/check-bootstrap-essential-tools-smoke.shs`; no parallel
  replacement wrappers.
- Manual `step("...")` helpers: N/A because the blocker regression is a
  compiler unit/integration contract rather than an operator scenario.
- Temporary placeholders: forbidden; any unavoidable temporary helper must
  terminate with `fail(...)` or `assert(false)` and cannot enter the candidate.
- Generated-manual review: N/A unless an executable scenario is added; if one
  is added, the primary agent owns docgen and operator-manual review.

## Phase

dev-done

## Log

- dev: Created the missing Stage 4 state file with ten acceptance criteria
  (type: bug) and separated backend-debug work from bootstrap evidence.
- dev: The bounded enum-payload focused setup exhausted three non-diagnostic
  reproducer shapes without source edits. Recorded the Stage 4 entry guard,
  ordinary-mode false green, declaration-only-to-materialized upgrade hazard,
  and the required executable HIR probe for the next scoped continuation.
- dev: The executable HIR probe reproduced the exact declaration-only upgrade
  at exit 34 with admitted pure-Simple Stage 3. Three bounded closure drafts
  ended at walker exit 60, so no compiler source was accepted. Review requires
  typed owner-local VariantKind extraction, physical-surface canonical owners,
  full terminal identity collision checks, and the missing TypeKind adjacent
  coverage before the next Stage 4 retry.
- dev: Added backend artifact identity and intermediate-layer boundary
  coverage. Fixed the discovered layer_result reason-clobber bug with exact
  Metal and adjacent CUDA/Vulkan fail-closed regressions; these tests are
  diagnostic evidence and do not satisfy the Stage 4 binary acceptance gates.
