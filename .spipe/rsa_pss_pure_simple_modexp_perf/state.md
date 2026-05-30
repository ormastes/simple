# Feature: rsa_pss_pure_simple_modexp_perf

## Raw Request
New task: Work in /home/ormastes/dev/pub/simple on tracker doc/08_tracking/feature_request/rsa_pss_pure_simple_modexp_perf_2026-05-02.md. You are not alone in the codebase: do not revert others' edits. Own only RSA-PSS/modexp pure Simple implementation/tests/docs plus .spipe/rsa_pss_pure_simple_modexp_perf/** and tracker. Use $sp_dev workflow. Do not solve by adding Rust; pure Simple is main. Implement next concrete perf/algorithm improvement or close with benchmark evidence, run focused crypto tests/benchmarks, update tracker. Report changed paths, tests, blockers.

## Task Type
feature

## Refined Goal
Improve or evidence-close the next open RSA-PSS pure Simple modular exponentiation performance item without adding Rust implementation code.

## Acceptance Criteria
- AC-1: The tracker identifies the selected next RSA-PSS/modexp performance item and records whether it was improved or closed with benchmark evidence.
- AC-2: Any implementation change is in pure Simple RSA-PSS/modexp code, not Rust, and preserves RSA-PSS correctness.
- AC-3: Focused RSA-PSS/modexp tests pass in interpreter mode.
- AC-4: A focused benchmark or performance probe runs and records before/after or current closure evidence.
- AC-5: Changed files stay within RSA-PSS/modexp pure Simple implementation/tests/docs, `.spipe/rsa_pss_pure_simple_modexp_perf/**`, and the tracker.

## Scope Exclusions
- No Rust implementation changes.
- No unrelated crypto, compiler, runtime, editor, docs, or generated artifact changes.
- No reverting edits made by others.

## Phase
dev-done

## Log
- dev: Created state file with 5 acceptance criteria (type: feature).
