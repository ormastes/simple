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
verify-done

## Log
- dev: Created state file with 5 acceptance criteria (type: feature).
- research: Existing tracker status is PARTIAL; remaining acceptance gap is RSA-2048 interpreter completion within 60s. Relevant implementation is `src/os/crypto/rsa_pss.spl` and `src/os/crypto/rsa_fallback.spl`; focused specs are `test/unit/lib/crypto/rsa_pss_sha256_kat_spec.spl`, `test/unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl`, `test/unit/lib/crypto/rsa_pkcs1_v15_spec.spl`, and `test/unit/os/crypto/rsa_contract_parity_spec.spl`.
- implement: Evaluated one additional pure-Simple PSS bigint micro-optimization (`_pss_bi_mul` zero/one short-circuit). It was correct but slower on the focused KAT, so it was reverted and no implementation diff was kept.
- verify: Current `HEAD` already contains the previously landed PSS bigint hot-path speedups. `rsa_pss_sha256_kat_spec.spl` measured 7014ms before warm/current reruns and 2302ms after reverting the rejected micro-optimization; `rsa_pss_sha256_roundtrip_slow_spec.spl` still timed out at 60s, so FR-CRYPTO-0001 remains PARTIAL.

## Research Summary
### Existing Code
- `src/os/crypto/rsa_pss.spl:46-230` — pure-Simple 30-bit limb bigint helpers and 4-bit sliding-window PSS modexp.
- `src/os/crypto/rsa_fallback.spl:67-312` — parallel PKCS#1 v1.5 pure-Simple bigint implementation with direct bit-mask extraction already present.
- `test/unit/lib/crypto/rsa_pss_sha256_kat_spec.spl` — fast RSA-PSS parser and argument-validation coverage.
- `test/unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl` — RSA-2048 PSS slow acceptance spec.
- `test/unit/lib/crypto/rsa_pkcs1_v15_spec.spl` — PKCS#1 v1.5 acceptance-related spec.

### Reusable Modules
- `os.crypto.rsa_pss` — target pure-Simple implementation.
- `os.crypto.rsa_fallback` — implementation pattern reference for bigint bit extraction.

### Domain Notes
- The remaining RSA-2048 cliff is still modular reduction cost during modexp; no further safe micro-optimization was kept because the attempted multiplication fast path regressed the focused KAT.

### Open Questions
- NONE

## Requirements
- REQ-1 (from AC-1): Tracker must record selected PSS bigint micro-optimization evaluation and current slow-spec status — area: `doc/08_tracking/feature_request/`.
- REQ-2 (from AC-2): Any kept implementation changes must remain pure Simple — area: `src/os/crypto/rsa_pss.spl`.
- REQ-3 (from AC-3): Focused RSA-PSS tests must pass in interpreter mode — area: `test/unit/lib/crypto/`.
- REQ-4 (from AC-4): Benchmark evidence must include before/after or current closure result — area: `.spipe/rsa_pss_pure_simple_modexp_perf/state.md`.
- REQ-5 (from AC-5): Changed paths must remain inside requested ownership scope.

## Implementation Summary
- No source implementation diff was kept.
- Attempted `_pss_bi_mul` zero/one short-circuit in `src/os/crypto/rsa_pss.spl`; reverted because it increased focused KAT time to 10390ms.
- No Rust implementation code was added.
- No shared RSA fallback behavior was changed.

## Verification Summary
- PASS: `SIMPLE_LIB=src bin/simple check src/os/crypto/rsa_pss.spl src/os/crypto/rsa_fallback.spl test/unit/lib/crypto/rsa_pss_sha256_kat_spec.spl test/unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl test/unit/lib/crypto/rsa_pkcs1_v15_spec.spl`.
- PASS: `SIMPLE_LIB=src bin/simple test test/unit/lib/crypto/rsa_pss_sha256_kat_spec.spl --mode=interpreter --clean --fail-fast` — 7 passed; reported spec time 2302ms after reverting the rejected micro-optimization. The rejected `_pss_bi_mul` short-circuit measured 10390ms and was not kept.
- PASS: `SIMPLE_LIB=src bin/simple test test/unit/lib/crypto/rsa_pss_smoke_spec.spl --mode=interpreter --clean --fail-fast` — 2 passed.
- PASS: `SIMPLE_LIB=src bin/simple test test/unit/os/crypto/rsa_contract_parity_spec.spl --mode=interpreter --clean --fail-fast` — 6 passed.
- FAIL/TIMEOUT: `timeout 60s env SIMPLE_LIB=src bin/simple test --only-slow test/unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl --mode=interpreter --clean --fail-fast` — timed out at 60s before and after this slice.
- FAIL: `SIMPLE_LIB=src bin/simple test test/unit/lib/crypto/rsa_pkcs1_v15_spec.spl --mode=interpreter --clean --fail-fast` — 9 passed, 1 failed; runner output did not include assertion details. This file was not changed in this slice.
